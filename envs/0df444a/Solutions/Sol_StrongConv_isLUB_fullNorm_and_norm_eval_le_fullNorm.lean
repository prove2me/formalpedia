-- Prove2me | solution 1 for StrongConv.isLUB_fullNorm_and_norm_eval_le_fullNorm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T08:16:18.834578+00:00
-- url     : https://prove2.me/submissions/e05573a6-9810-4894-9c0a-4367fb7daa11

import Definitions.Def_StrongConv

universe u

noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace

namespace StrongConvChoi
open StrongConv

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, Finset.sum_apply, Pi.single_apply]

lemma eval_apply {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin D => H)) (a : Fin D) :
    (P.eval u x) a = ∑ w ∈ P.support, ∑ b, P w a b • wordOp u w (x b) := by
  simp [NCPoly.eval, tensorOp_apply]

/-- A word given as a list of letters. -/
def wordL {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : List (Fin d ⊕ Fin d)) : H →L[ℂ] H :=
  (l.map (letterOp u)).prod

lemma wordOp_eq {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u w = wordL u w.toList := rfl

lemma wordL_nil {d : ℕ} (u : Fin d → H →L[ℂ] H) : wordL u [] = 1 := by simp [wordL]

lemma wordL_cons {d : ℕ} (u : Fin d → H →L[ℂ] H) (x : Fin d ⊕ Fin d) (l : List (Fin d ⊕ Fin d)) :
    wordL u (x :: l) = letterOp u x * wordL u l := by simp [wordL]

lemma letterOp_mem_unitary {d : ℕ} {u : Fin d → H →L[ℂ] H} (hu : ∀ i, u i ∈ unitary (H →L[ℂ] H))
    (x : Fin d ⊕ Fin d) : letterOp u x ∈ unitary (H →L[ℂ] H) := by
  cases x with
  | inl i => exact hu i
  | inr i => exact Unitary.star_mem (hu i)

lemma wordL_mem_unitary {d : ℕ} {u : Fin d → H →L[ℂ] H} (hu : ∀ i, u i ∈ unitary (H →L[ℂ] H))
    (l : List (Fin d ⊕ Fin d)) : wordL u l ∈ unitary (H →L[ℂ] H) := by
  induction l with
  | nil => rw [wordL_nil]; exact one_mem _
  | cons x l ih => rw [wordL_cons]; exact mul_mem (letterOp_mem_unitary hu x) ih

lemma norm_le_one_of_mem_unitary {T : H →L[ℂ] H} (hT : T ∈ unitary (H →L[ℂ] H)) : ‖T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary hT]; simp

lemma norm_tensorOp_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    ‖tensorOp A T‖ ≤ (∑ a, ∑ b, ‖A a b‖) * ‖T‖ := by
  unfold tensorOp
  rw [Finset.sum_mul]
  refine le_trans (norm_sum_le (E := PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H))
    _ _) (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine le_trans (norm_sum_le (E := PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H))
    _ _) (Finset.sum_le_sum fun b _ => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  calc _ = ‖T (x b)‖ := PiLp.norm_toLp_single _ _ _ _
    _ ≤ ‖T‖ * ‖x b‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖x‖ := mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x b) (norm_nonneg _)

lemma norm_eval_le_of_unitary {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (hu : ∀ i, u i ∈ unitary (H →L[ℂ] H)) :
    ‖P.eval u‖ ≤ ∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖ := by
  unfold NCPoly.eval
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  refine (norm_tensorOp_le _ _).trans ?_
  have h1 : ‖wordOp u w‖ ≤ 1 := norm_le_one_of_mem_unitary (wordL_mem_unitary hu _)
  have h0 : 0 ≤ ∑ a, ∑ b, ‖P w a b‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc _ ≤ (∑ a, ∑ b, ‖P w a b‖) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

end General

lemma toEuclideanCLM_mem_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ) ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) U.2

/-- The set whose supremum is `fullNorm`. -/
def valSet {D d : ℕ} (P : NCPoly D d) : Set ℝ :=
  {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
        x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖}

lemma valSet_nonempty {D d : ℕ} (P : NCPoly D d) : (valSet P).Nonempty :=
  ⟨_, 0, fun _ => 1, rfl⟩

lemma valSet_bddAbove {D d : ℕ} (P : NCPoly D d) : BddAbove (valSet P) := by
  refine ⟨∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖, ?_⟩
  rintro x ⟨n, U, rfl⟩
  exact norm_eval_le_of_unitary P _ fun i => toEuclideanCLM_mem_unitary (U i)

lemma isLUB_fullNorm {D d : ℕ} (P : NCPoly D d) : IsLUB (valSet P) P.fullNorm :=
  isLUB_csSup (valSet_nonempty P) (valSet_bddAbove P)

lemma le_fullNorm {D d : ℕ} (P : NCPoly D d) {n : ℕ} (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ) :
    ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖ ≤
      P.fullNorm :=
  le_csSup (valSet_bddAbove P) ⟨n, U, rfl⟩

section Dilation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary restricted to a subspace `S'` of `E` that it maps into `E`. -/
def isoOn (E : Submodule ℂ H) (S' : Submodule ℂ E) (T : H →L[ℂ] H)
    (hT : T ∈ unitary (H →L[ℂ] H)) (h : ∀ x : S', T ((x : E) : H) ∈ E) : S' →ₗᵢ[ℂ] E where
  toLinearMap := LinearMap.codRestrict E ((T : H →ₗ[ℂ] H) ∘ₗ E.subtype ∘ₗ S'.subtype) h
  norm_map' x := by
    change ‖T ((x : E) : H)‖ = ‖((x : E) : H)‖
    exact ContinuousLinearMap.norm_map_of_mem_unitary hT _

theorem exists_unitary_ext (E : Submodule ℂ H) [FiniteDimensional ℂ E] (S : Submodule ℂ H)
    (T : H →L[ℂ] H) (hT : T ∈ unitary (H →L[ℂ] H)) (hTS : ∀ x ∈ S, T x ∈ E) :
    ∃ g : E ≃ₗᵢ[ℂ] E, ∀ x : E, (x : H) ∈ S → ((g x : E) : H) = T x := by
  let S' : Submodule ℂ E := S.comap E.subtype
  let f := isoOn E S' T hT (fun x => hTS _ x.2)
  refine ⟨f.extend.toLinearIsometryEquiv rfl, fun x hx => ?_⟩
  have := LinearIsometry.extend_apply f ⟨x, hx⟩
  change ((f.extend x : E) : H) = _
  rw [this]
  rfl

/-- The unitary matrix of a linear isometric automorphism of `ℂⁿ`. -/
def matOf {n : ℕ} (W : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm (W : _ →L[ℂ] _),
    Unitary.map_mem (R := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (S := Matrix (Fin n) (Fin n) ℂ)
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm :
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
      (Unitary.linearIsometryEquiv.symm W).2⟩

lemma toEuclideanCLM_matOf {n : ℕ}
    (W : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (matOf W : Matrix (Fin n) (Fin n) ℂ) =
      (W : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).apply_symm_apply _

theorem exists_matrix_model (E : Submodule ℂ H) [FiniteDimensional ℂ E] {d : ℕ}
    (g : Fin d → (E ≃ₗᵢ[ℂ] E)) :
    ∃ (n : ℕ) (V : Fin d → Matrix.unitaryGroup (Fin n) ℂ) (e : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ i y, Matrix.toEuclideanCLM (𝕜 := ℂ) (V i : Matrix (Fin n) (Fin n) ℂ) y = e (g i (e.symm y)) ∧
        star (Matrix.toEuclideanCLM (𝕜 := ℂ) (V i : Matrix (Fin n) (Fin n) ℂ)) y =
          e ((g i).symm (e.symm y)) := by
  obtain ⟨e⟩ : Nonempty (E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :=
    ⟨(stdOrthonormalBasis ℂ E).repr⟩
  refine ⟨_, fun i => matOf (e.symm.trans ((g i).trans e)), e, fun i y => ⟨?_, ?_⟩⟩
  · rw [toEuclideanCLM_matOf]
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.trans_apply]
  · rw [toEuclideanCLM_matOf, LinearIsometryEquiv.star_eq_symm]
    rfl

/-- The finite-dimensional unitary dilation: every finite set `G` of vectors is reproduced, letter by
letter, by unitary matrices acting on a finite-dimensional subspace of `H`. -/
theorem exists_dilation {d : ℕ} (U : Fin d → H →L[ℂ] H) (hU : ∀ i, U i ∈ unitary (H →L[ℂ] H))
    (G : Set H) (hG : G.Finite) :
    ∃ (n : ℕ) (V : Fin d → Matrix.unitaryGroup (Fin n) ℂ)
      (J : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] H),
      (∀ g ∈ G, ∃ y, J y = g) ∧
      ∀ y, J y ∈ G → ∀ l : Fin d ⊕ Fin d,
        J (letterOp (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (V i : Matrix (Fin n) (Fin n) ℂ))
          l y) = letterOp U l (J y) := by
  classical
  obtain ⟨Gs, hGs_def⟩ : ∃ Gs : Set H, Gs = G ∪ ⋃ i, ⇑(star (U i)) '' G := ⟨_, rfl⟩
  have hGs : Gs.Finite := hGs_def ▸ hG.union (Set.finite_iUnion fun i => hG.image _)
  obtain ⟨Ef, hEf_def⟩ : ∃ Ef : Set H, Ef = Gs ∪ ⋃ i, ⇑(U i) '' Gs := ⟨_, rfl⟩
  have hEf : Ef.Finite := hEf_def ▸ hGs.union (Set.finite_iUnion fun i => hGs.image _)
  obtain ⟨E, hE_def⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ Ef := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ E := hE_def ▸ FiniteDimensional.span_of_finite ℂ hEf
  obtain ⟨S, hS_def⟩ : ∃ S : Submodule ℂ H, S = Submodule.span ℂ Gs := ⟨_, rfl⟩
  have hGsE : Gs ⊆ E := fun x hx => hE_def ▸ Submodule.subset_span (hEf_def ▸ Or.inl hx)
  have hGGs : G ⊆ Gs := fun x hx => hGs_def ▸ Or.inl hx
  have hGsS : Gs ⊆ S := fun x hx => hS_def ▸ Submodule.subset_span hx
  have hUS : ∀ i, ∀ x ∈ S, U i x ∈ E := by
    intro i x hx
    have : S.map (U i : H →ₗ[ℂ] H) ≤ E := by
      rw [hS_def, Submodule.map_span, hE_def]
      exact Submodule.span_le.2 fun y hy =>
        Submodule.subset_span (hEf_def ▸ Or.inr (Set.mem_iUnion.2 ⟨i, hy⟩))
    exact this (Submodule.mem_map_of_mem hx)
  choose g hg using fun i => exists_unitary_ext E S (U i) (hU i) (hUS i)
  obtain ⟨n, V, e, hVe⟩ := exists_matrix_model E g
  let J : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] H := E.subtypeₗᵢ.comp e.symm.toLinearIsometry
  have hJ : ∀ y, J y = ((e.symm y : E) : H) := fun y => rfl
  refine ⟨n, V, J, fun x hx => ⟨e ⟨x, hGsE (hGGs hx)⟩, by simp [hJ]⟩, ?_⟩
  intro y hy l
  cases l with
  | inl i =>
    simp only [letterOp]
    rw [(hVe i y).1, hJ, hJ, LinearIsometryEquiv.symm_apply_apply]
    exact hg i _ (hGsS (hGGs hy))
  | inr i =>
    simp only [letterOp]
    rw [(hVe i y).2, hJ, hJ, LinearIsometryEquiv.symm_apply_apply]
    have hzG : ((e.symm y : E) : H) ∈ G := hy
    have hmem : star (U i) ((e.symm y : E) : H) ∈ Gs :=
      hGs_def ▸ Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_image_of_mem _ hzG⟩)
    let z' : E := ⟨star (U i) ((e.symm y : E) : H), hGsE hmem⟩
    have hgz : g i z' = e.symm y := by
      apply Subtype.ext
      rw [hg i z' (hGsS hmem)]
      change (U i * star (U i)) ((e.symm y : E) : H) = _
      rw [Unitary.mul_star_self_of_mem (hU i)]
      rfl
    have : (g i).symm (e.symm y) = z' := by rw [← hgz]; simp
    rw [this]

end Dilation

section Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_eval_le_fullNorm {D d : ℕ} (P : NCPoly D d) (U : Fin d → H →L[ℂ] H)
    (hU : ∀ i, U i ∈ unitary (H →L[ℂ] H)) : ‖P.eval U‖ ≤ P.fullNorm := by
  classical
  have hnn : 0 ≤ P.fullNorm := (norm_nonneg _).trans (le_fullNorm P (n := 0) fun _ => 1)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun ξ => ?_
  -- the finite set of vectors the evaluation touches
  set G : Set H := Set.range (fun b => ξ b) ∪
    ⋃ w ∈ (P.support : Set (FreeMonoid (Fin d ⊕ Fin d))),
      ⋃ l ∈ {l | l ∈ w.toList.tails}, Set.range (fun b => wordL U l (ξ b)) with hG_def
  have hG : G.Finite :=
    (Set.finite_range _).union <| Set.Finite.biUnion (Finset.finite_toSet _) fun w _ =>
      Set.Finite.biUnion (List.finite_toSet _) fun l _ => Set.finite_range _
  obtain ⟨n, V, J, hJG, hJl⟩ := exists_dilation U hU G hG
  set V' := fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (V i : Matrix (Fin n) (Fin n) ℂ)
  choose y hy using fun b => hJG (ξ b) (Or.inl ⟨b, rfl⟩)
  -- words act compatibly along suffixes lying in `G`
  have hword : ∀ (l : List (Fin d ⊕ Fin d)) (z : EuclideanSpace ℂ (Fin n)),
      (∀ l', l' <:+ l → wordL U l' (J z) ∈ G) → J (wordL V' l z) = wordL U l (J z) := by
    intro l
    induction l with
    | nil => intro z _; simp [wordL_nil]
    | cons x l ih =>
      intro z hz
      have ih' := ih z fun l' hl' => hz l' (hl'.trans (List.suffix_cons x l))
      have hmem : J (wordL V' l z) ∈ G := by
        rw [ih']; exact hz l (List.suffix_cons x l)
      rw [wordL_cons, wordL_cons, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        hJl _ hmem, ih']
  set η : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin n)) := WithLp.toLp 2 y
  have hcomp : ∀ a, (P.eval U ξ) a = J ((P.eval V' η) a) := by
    intro a
    rw [eval_apply, eval_apply, map_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearIsometry.map_smul, wordOp_eq, wordOp_eq]
    have hηb : η b = y b := rfl
    rw [hηb, hword, hy]
    intro l' hl'
    rw [hy]
    refine Or.inr ?_
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, l', (List.mem_tails _ _).2 hl', b, rfl⟩
  have hnorm1 : ‖P.eval U ξ‖ = ‖P.eval V' η‖ := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcomp, LinearIsometry.norm_map]
  have hnorm2 : ‖η‖ = ‖ξ‖ := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have hηb : η b = y b := rfl
    rw [hηb, ← hy b, LinearIsometry.norm_map]
  calc ‖P.eval U ξ‖ = ‖P.eval V' η‖ := hnorm1
    _ ≤ ‖P.eval V'‖ * ‖η‖ := (P.eval V').le_opNorm η
    _ ≤ P.fullNorm * ‖ξ‖ := by
      rw [hnorm2]
      exact mul_le_mul_of_nonneg_right (le_fullNorm P V) (norm_nonneg _)

end Main

theorem isLUB_fullNorm_and_norm_eval_le_fullNorm_dev {D d : ℕ} (P : NCPoly D d) :
    IsLUB {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
        x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖}
      P.fullNorm ∧
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : Fin d → H →L[ℂ] H), (∀ i, U i ∈ unitary (H →L[ℂ] H)) → ‖P.eval U‖ ≤ P.fullNorm :=
  ⟨isLUB_fullNorm P, fun _ _ _ _ U hU => norm_eval_le_fullNorm P U hU⟩

end StrongConvChoi

open StrongConv in
theorem solution {D d : ℕ} (P : NCPoly D d) :
    IsLUB {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
        x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖}
      P.fullNorm ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : Fin d → H →L[ℂ] H), (∀ i, U i ∈ unitary (H →L[ℂ] H)) → ‖P.eval U‖ ≤ P.fullNorm :=
  StrongConvChoi.isLUB_fullNorm_and_norm_eval_le_fullNorm_dev P
