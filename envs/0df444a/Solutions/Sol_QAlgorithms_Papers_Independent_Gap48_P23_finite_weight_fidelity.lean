-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.finite_weight_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:40:53.033325+00:00
-- url     : https://prove2.me/submissions/495af70a-8b53-4455-852b-abac77218af5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem g74h_effectProb_conj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (A B : Op (Fin d)) :
    effectProb (conjSuperop U.val A) (conjSuperop U.val B) = effectProb A B := by
  have hU : (U.val)ᴴ * U.val = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold effectProb conjSuperop
  congr 1
  have : U.val * A * (U.val)ᴴ * (U.val * B * (U.val)ᴴ) = U.val * (A * B) * (U.val)ᴴ := by
    calc U.val * A * (U.val)ᴴ * (U.val * B * (U.val)ᴴ)
        = U.val * A * ((U.val)ᴴ * U.val) * B * (U.val)ᴴ := by simp only [Matrix.mul_assoc]
      _ = U.val * (A * B) * (U.val)ᴴ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem g74h_conj_perm_single {I : Type*} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (x : I) :
    conjSuperop (QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix σ)
      (Matrix.single x x (1 : ℂ)) = Matrix.single (σ x) (σ x) 1 := by
  ext a b
  simp only [conjSuperop, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
    QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix]
  have e : ∀ c : I, (b = σ c) = (c = σ.symm b) := fun c => by
    apply propext; constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [e]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
  by_cases ha : a = σ x <;> by_cases hb : b = σ x <;> simp [ha, hb, eq_comm, Equiv.eq_symm_apply]

theorem g74h_tensorPower_perm {n : ℕ} (τ : Equiv.Perm (Fin 2)) :
    tensorPower n (QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix τ) =
      QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix
        (Equiv.arrowCongr (Equiv.refl (Fin n)) τ) := by
  ext a b
  simp only [tensorPower, QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  congr 1
  apply propext
  simp [funext_iff]

theorem g74h_card_rep (n h : ℕ) (hh : h ≤ n) : booleanWordWeight (weightRepresentative n h) = h := by
  unfold booleanWordWeight weightRepresentative
  have : (Finset.univ.filter (fun i : Fin n => (if i.val < n - h then (0 : Fin 2) else 1) = 1)).map
      Fin.valEmbedding = Finset.Ico (n - h) n := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, i.isLt⟩
      by_contra hc
      simp [show i.val < n - h by omega] at hi
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, h2⟩, by simp [show ¬ m < n - h by omega], rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ico]
  omega

theorem g74h_card_zero {n : ℕ} (x : Word n 2) :
    (Finset.univ.filter (fun i => x i = 0)).card = n - booleanWordWeight x := by
  unfold booleanWordWeight
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => x i = 1)
  have e : (Finset.univ.filter (fun i => ¬ x i = 1)) = Finset.univ.filter (fun i => x i = 0) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi; rcases (show ∀ c : Fin 2, c = 0 ∨ c = 1 by decide) (x i) with h' | h' <;> simp_all
    · intro hi; simp [hi]
  rw [e, Finset.card_univ, Fintype.card_fin] at h
  omega

theorem g74h_exists_perm {n : ℕ} (x y : Word n 2) (hw : booleanWordWeight x = booleanWordWeight y) :
    ∃ p : Equiv.Perm (Fin n), permuteWord p x = y := by
  have hc : ∀ c : Fin 2, Fintype.card {a // x a = c} = Fintype.card {b // y b = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    fin_cases c
    · show (Finset.univ.filter (fun i => x i = 0)).card = (Finset.univ.filter (fun i => y i = 0)).card
      rw [g74h_card_zero, g74h_card_zero, hw]
    · exact hw
  let e := Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c))
  refine ⟨e, ?_⟩
  funext b
  simp only [permuteWord, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
  have := Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hc c)) (e.symm b)
  rw [show Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)) (e.symm b) = b from
    e.apply_symm_apply b] at this
  exact this.symm

theorem solution (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (f : Word n 2 → Fin 2) (hf : WordSymmetric f) (he : Equivariant f)
    (Phi : Superop (Word n 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hp : PermutationInvariant Phi) (hu : WordUnitaryEquivariant Phi) :
    IsLeast {r | ∃ h : TwoRowShape n, r = effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1))}
      (functionFidelity (fun _ => True) f Phi) := by
  obtain ⟨g, hg⟩ : ∃ g : Word n 2 → ℝ, ∀ x, g x =
      effectProb (Matrix.single (f x) (f x) 1) (Phi (Matrix.single x x 1)) := ⟨_, fun _ => rfl⟩
  have hU : ∀ x U, inputFidelity f Phi x U = g x := by
    intro x U
    rw [hg, inputFidelity, encodedInput, targetDensity, hu, g74h_effectProb_conj]
  have hP : ∀ x (p : Equiv.Perm (Fin n)), g (permuteWord p x) = g x := by
    intro x p
    rw [hg, hg, hf p x]
    rw [show Matrix.single (permuteWord p x) (permuteWord p x) (1:ℂ) =
      conjSuperop (wordPermutationMatrix n 2 p) (Matrix.single x x 1) from
      (g74h_conj_perm_single _ x).symm, hp]
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let X : Op (Fin 2) := QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix σ
  have hX : X ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [X, σ, QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, Equiv.swap_apply_def]
  have hF : ∀ x, g (σ ∘ x) = g x := by
    intro x
    rw [hg, hg, he σ x]
    have h1 : Matrix.single (σ (f x)) (σ (f x)) (1 : ℂ) = conjSuperop X (Matrix.single (f x) (f x) 1) :=
      (g74h_conj_perm_single σ (f x)).symm
    have h2 : Phi (Matrix.single (σ ∘ x) (σ ∘ x) 1) = conjSuperop X (Phi (Matrix.single x x 1)) := by
      rw [← hu ⟨X, hX⟩]
      show _ = Phi (conjSuperop (tensorPower n X) _)
      rw [g74h_tensorPower_perm, g74h_conj_perm_single]
      rfl
    rw [h1, h2]
    exact g74h_effectProb_conj ⟨X, hX⟩ _ _
  have hwF : ∀ x : Word n 2, booleanWordWeight (σ ∘ x) = n - booleanWordWeight x := by
    intro x
    rw [← g74h_card_zero]
    unfold booleanWordWeight
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, σ]
    rcases (show ∀ c : Fin 2, c = 0 ∨ c = 1 by decide) (x i) with h' | h' <;> simp [h', Equiv.swap_apply_def]
  have hwle : ∀ x : Word n 2, booleanWordWeight x ≤ n := by
    intro x
    unfold booleanWordWeight
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hrep : ∀ x, ∃ h : TwoRowShape n, g x = g (weightRepresentative n h.val) := by
    intro x
    by_cases hx : booleanWordWeight x ≤ n / 2
    · refine ⟨⟨booleanWordWeight x, by omega⟩, ?_⟩
      obtain ⟨p, hp⟩ := g74h_exists_perm x (weightRepresentative n (booleanWordWeight x))
        (by rw [g74h_card_rep _ _ (hwle x)])
      rw [← hp, hP]
    · have hle := hwle x
      refine ⟨⟨n - booleanWordWeight x, by omega⟩, ?_⟩
      obtain ⟨p, hp⟩ := g74h_exists_perm (σ ∘ x) (weightRepresentative n (n - booleanWordWeight x))
        (by rw [g74h_card_rep _ _ (by omega), hwF])
      show g x = g (weightRepresentative n (n - booleanWordWeight x))
      rw [← hp, hP, hF]
  have hset : fidelityValues (fun _ => True) f Phi = {r | ∃ h : TwoRowShape n, r = effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1))} := by
    ext r
    simp only [fidelityValues, Set.mem_setOf_eq, true_and]
    constructor
    · rintro ⟨x, U, rfl⟩
      obtain ⟨h, hh⟩ := hrep x
      exact ⟨h, by rw [hU, hh, hg]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨weightRepresentative n h.val, 1, by rw [hU, hg]⟩
  have hfin : {r | ∃ h : TwoRowShape n, r = effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1))}.Finite := by
    have := Set.finite_range (fun h : TwoRowShape n => effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1)))
    refine this.subset ?_
    rintro r ⟨h, rfl⟩
    exact ⟨h, rfl⟩
  have hne : {r | ∃ h : TwoRowShape n, r = effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1))}.Nonempty :=
    ⟨_, ⟨0, rfl⟩⟩
  unfold functionFidelity
  rw [hset]
  exact ⟨hne.csInf_mem hfin, fun r hr => csInf_le hfin.bddBelow hr⟩

end
