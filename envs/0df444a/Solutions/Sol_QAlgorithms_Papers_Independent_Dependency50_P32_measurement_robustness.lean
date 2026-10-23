-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P32.measurement_robustness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:55:40.137226+00:00
-- url     : https://prove2.me/submissions/24766c2d-0484-4b12-933f-e874f637eefc

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32.X7B12M

open QAlgorithms

/-! ### Choi matrix of a measurement family: linear and injective -/

lemma X7_mc_apply {x a d : ℕ+} (M : MeasurementFamily x a d) (p q) :
    measurementChoi M p q = if p.2 = q.2 then
      ∑ s : Fin x, ∑ i : Fin d, ∑ j : Fin d,
        M s p.2 i j * (Matrix.single p.1 q.1 (1 : ℂ)) (finProdFinEquiv (s, j))
          (finProdFinEquiv (s, i)) else 0 := rfl

lemma X7_mc_lin {x a d : ℕ+} (A B : MeasurementFamily x a d) (c : ℂ) :
    measurementChoi (fun s o => A s o + c • B s o) =
      measurementChoi A + c • measurementChoi B := by
  funext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, X7_mc_apply]
  split_ifs
  · simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  · simp

lemma X7_mc_smul {x a d : ℕ+} (A : MeasurementFamily x a d) (c : ℂ) :
    measurementChoi (fun s o => c • A s o) = c • measurementChoi A := by
  funext p q
  simp only [Matrix.smul_apply, X7_mc_apply]
  split_ifs
  · simp [Finset.mul_sum, mul_assoc]
  · simp

lemma X7_mc_entry {x a d : ℕ+} (M : MeasurementFamily x a d) (s : Fin x) (o : Fin a)
    (i j : Fin d) :
    measurementChoi M (finProdFinEquiv (s, j), o) (finProdFinEquiv (s, i), o) = M s o i j := by
  show (if o = o then ∑ s' : Fin x, ∑ i' : Fin d, ∑ j' : Fin d, M s' o i' j' *
      (Matrix.single (finProdFinEquiv (s, j)) (finProdFinEquiv (s, i)) (1 : ℂ) :
        Matrix (Fin ((x : ℕ) * d)) (Fin ((x : ℕ) * d)) ℂ)
        (finProdFinEquiv (s', j')) (finProdFinEquiv (s', i')) else 0) = M s o i j
  rw [if_pos rfl]
  have key : ∀ (s' : Fin x) (i' j' : Fin d),
      (Matrix.single (finProdFinEquiv (s, j)) (finProdFinEquiv (s, i)) (1 : ℂ) :
        Matrix (Fin ((x : ℕ) * d)) (Fin ((x : ℕ) * d)) ℂ)
        (finProdFinEquiv (s', j')) (finProdFinEquiv (s', i')) =
      if s' = s ∧ i' = i ∧ j' = j then 1 else 0 := by
    intro s' i' j'
    rw [Matrix.single_apply]
    by_cases h : s' = s ∧ i' = i ∧ j' = j
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · rw [if_neg h, if_neg]
      intro hh
      apply h
      have h1 := Prod.ext_iff.mp (finProdFinEquiv.injective hh.1)
      have h2 := Prod.ext_iff.mp (finProdFinEquiv.injective hh.2)
      exact ⟨h1.1.symm, h2.2.symm, h1.2.symm⟩
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb
      apply Finset.sum_eq_zero; intro c _
      simp [hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro e _
    simp [hb]
  · simp

lemma X7_mc_inj {x a d : ℕ+} {A B : MeasurementFamily x a d}
    (h : measurementChoi A = measurementChoi B) : A = B := by
  funext s o i j
  rw [← X7_mc_entry A, ← X7_mc_entry B, h]

lemma X7_mc_eq_iff {x a d : ℕ+} (M N F : MeasurementFamily x a d) (r : ℝ) :
    measurementChoi M + (r : ℂ) • measurementChoi N = ((1 + r : ℝ) : ℂ) • measurementChoi F ↔
      ∀ s o, M s o + (r : ℂ) • N s o = ((1 + r : ℝ) : ℂ) • F s o := by
  rw [← X7_mc_lin, ← X7_mc_smul]
  constructor
  · intro h s o
    have := X7_mc_inj h
    exact congrFun (congrFun this s) o
  · intro h
    congr 1
    funext s o
    exact h s o

/-! ### Positivity and compactness -/

open scoped MatrixOrder in
lemma X7_fac {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, A = Bᴴ * B := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, rfl⟩

lemma X7_trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := X7_fac hA
  obtain ⟨D, rfl⟩ := X7_fac hB
  have : (Cᴴ * C * (Dᴴ * D)).trace = ((C * Dᴴ)ᴴ * (C * Dᴴ)).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [this]
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1

lemma X7_compl_psd {O n : Type*} [Fintype O] [Fintype n] [DecidableEq n] [DecidableEq O]
    (N : O → Matrix n n ℂ) (hN : IsPOVM N) (o : O) : (1 - N o).PosSemidef := by
  have : 1 - N o = ∑ o' ∈ Finset.univ.erase o, N o' := by
    rw [← hN.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ o)]; abel
  rw [this]
  exact Matrix.posSemidef_sum _ (fun o' _ => hN.1 o')

lemma X7_entry_bound {O n : Type*} [Fintype O] [Fintype n] [DecidableEq n] [DecidableEq O]
    (N : O → Matrix n n ℂ) (hN : IsPOVM N) (o : O) (i j : n) :
    ‖N o i j‖ ≤ Fintype.card n := by
  set A := N o with hAdef
  have hA : A.PosSemidef := hN.1 o
  have hB : (1 - A).PosSemidef := X7_compl_psd N hN o
  have h1 := X7_trace_nonneg hA hB
  have h2 : 0 ≤ (1 - A).trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hAA : (A * A).trace.re = ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [← hA.1.apply l k]
    rw [show A k l * star (A k l) = ((Complex.normSq (A k l) : ℝ) : ℂ) from Complex.mul_conj _]
    rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hexp : (A * (1 - A)).trace.re = A.trace.re - (A * A).trace.re := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re]
  have hexp2 : (1 - A).trace.re = Fintype.card n - A.trace.re := by
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_one]; simp
  have hle : ‖A i j‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 := by
    calc ‖A i j‖ ^ 2 ≤ ∑ l, ‖A i l‖ ^ 2 :=
          Finset.single_le_sum (f := fun l => ‖A i l‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ∑ l, ‖A k l‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have hc : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hn := norm_nonneg (A i j)
  nlinarith

lemma X7_closed_psd {n : Type*} [Fintype n] [DecidableEq n] :
    IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  have : {A : Matrix n n ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ v : n → ℂ, {A | 0 ≤ star v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  apply IsClosed.inter
  · exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  · apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

lemma X7_povm_closed {O n : Type*} [Fintype O] [Fintype n] [DecidableEq n] :
    IsClosed {N : O → Matrix n n ℂ | IsPOVM N} := by
  have : {N : O → Matrix n n ℂ | IsPOVM N} =
      (⋂ o, (fun N : O → Matrix n n ℂ => N o) ⁻¹' {A | A.PosSemidef}) ∩ {N | ∑ o, N o = 1} := by
    ext N; simp [IsPOVM]
  rw [this]
  apply IsClosed.inter
  · exact isClosed_iInter fun o => X7_closed_psd.preimage (continuous_apply o)
  · exact isClosed_eq (continuous_finset_sum _ fun o _ => continuous_apply o) continuous_const

lemma X7_povm_compact {O n : Type*} [Fintype O] [Fintype n] [DecidableEq n] [DecidableEq O] :
    IsCompact {N : O → Matrix n n ℂ | IsPOVM N} := by
  have hc : IsCompact ((fun f : O → n → n → ℂ => fun o => Matrix.of (f o)) ''
      Set.univ.pi fun _ : O => Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
        Metric.closedBall (0 : ℂ) (Fintype.card n)) := by
    apply IsCompact.image
    · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        isCompact_closedBall _ _
    · exact continuous_pi fun o => continuous_matrix fun i j =>
        (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply o))
  apply hc.of_isClosed_subset X7_povm_closed
  intro N hN
  refine ⟨fun o i j => N o i j, ?_, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro o i j
  exact X7_entry_bound N hN o i j

/-! ### Joint measurements -/

def X7_marg {x a d : ℕ+} (G : (Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ) :
    MeasurementFamily x a d :=
  fun s o => ∑ ω ∈ Finset.univ.filter (fun ω : Fin x → Fin a => ω s = o), G ω

lemma X7_marg_valid {x a d : ℕ+} {G : (Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ}
    (hG : IsPOVM G) : ValidMeasurements (X7_marg G) := by
  intro s
  constructor
  · intro o; exact Matrix.posSemidef_sum _ (fun ω _ => hG.1 ω)
  · rw [← hG.2]
    exact Finset.sum_fiberwise Finset.univ (fun ω : Fin x → Fin a => ω s) G

lemma X7_marg_compat {x a d : ℕ+} {G : (Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ}
    (hG : IsPOVM G) : CompatiblePOVMs (X7_marg G) := by
  refine ⟨X7_marg_valid hG, ⟨Fintype.card (Fin x → Fin a), Fintype.card_pos⟩,
    fun i => G ((Fintype.equivFin (Fin x → Fin a)).symm i),
    fun o s i => if (Fintype.equivFin (Fin x → Fin a)).symm i s = o then 1 else 0,
    ⟨fun i => hG.1 _, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hG.2]
    exact Equiv.sum_comp (Fintype.equivFin (Fin x → Fin a)).symm G
  · intro o s i; dsimp only; split_ifs <;> norm_num
  · intro s i; simp
  · intro s o
    unfold X7_marg
    rw [Finset.sum_filter]
    rw [← Equiv.sum_comp (Fintype.equivFin (Fin x → Fin a)).symm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (Fintype.equivFin (Fin x → Fin a)).symm i s = o <;> simp [h]

lemma X7_inner_sum {x a : ℕ+} (q : Fin a → Fin x → ℝ) (hq1 : ∀ s, ∑ o, q o s = 1)
    (s : Fin x) (o : Fin a) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin x → Fin a => ω s = o), ∏ s', q (ω s') s' = q o s := by
  let f : Fin x → Fin a → ℝ := fun s' o' => if s' = s then (if o' = o then q o' s' else 0)
    else q o' s'
  have hL : ∏ s', ∑ o', f s' o' = q o s := by
    have : ∀ s', ∑ o', f s' o' = if s' = s then q o s else 1 := by
      intro s'
      by_cases h : s' = s
      · subst h; simp [f]
      · simp [f, h, hq1 s']
    simp only [this]
    rw [Finset.prod_ite_eq']; simp
  rw [← hL, Fintype.prod_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω s = o
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro s' _
    by_cases hs : s' = s
    · subst hs; simp [f, h]
    · simp [f, hs]
  · rw [if_neg h]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [f, h]

lemma X7_compat_joint {x a d : ℕ+} {F : MeasurementFamily x a d} (hF : CompatiblePOVMs F) :
    ∃ G : (Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ, IsPOVM G ∧ F = X7_marg G := by
  obtain ⟨_, k, P, q, hP, hq0, hq1, hFq⟩ := hF
  refine ⟨fun ω => ∑ i, (((∏ s, q (ω s) s i : ℝ)) : ℂ) • P i, ⟨?_, ?_⟩, ?_⟩
  · intro ω
    apply Matrix.posSemidef_sum
    intro i _
    apply (hP.1 i).smul
    exact Complex.zero_le_real.mpr (Finset.prod_nonneg fun s _ => hq0 _ _ _)
  · rw [Finset.sum_comm]
    rw [← hP.2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    have : ∑ ω : Fin x → Fin a, ∏ s, q (ω s) s i = 1 := by
      rw [← Fintype.prod_sum (fun s o => q o s i)]
      exact Finset.prod_eq_one fun s _ => hq1 s i
    rw [← Complex.ofReal_sum, this]; simp
  · funext s o
    rw [hFq s o]
    unfold X7_marg
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul, ← Complex.ofReal_sum,
      X7_inner_sum (fun o s => q o s i) (fun s => hq1 s i) s o]

/-! ### Feasibility and attainment -/

lemma X7_feasible {x a d : ℕ+} (M : MeasurementFamily x a d) (hM : ValidMeasurements M) :
    ∃ N F : MeasurementFamily x a d, ValidMeasurements N ∧ CompatiblePOVMs F ∧
      ∀ s o, M s o + (((a : ℕ) : ℝ) : ℂ) • N s o = ((1 + ((a : ℕ) : ℝ) : ℝ) : ℂ) • F s o := by
  have ha : (((a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.pos
    exact_mod_cast this.ne'
  have ha' : ((a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast a.pos.ne'
  set c : ℂ := ((((a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) with hc
  have hc0 : 0 ≤ c := Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsum1 : ∑ _o : Fin a, c • (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hc]
    split_ifs
    · rw [nsmul_eq_mul]; push_cast; field_simp
    · simp
  refine ⟨fun s o => c • ((1 - M s o) + c • 1), fun _ _ => c • 1, ?_, ?_, ?_⟩
  · intro s
    constructor
    · intro o
      exact ((X7_compl_psd _ (hM s) o).add (Matrix.PosSemidef.one.smul hc0)).smul hc0
    · rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, (hM s).2,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum1]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        smul_eq_mul, hc]
      split_ifs
      · rw [nsmul_eq_mul]; push_cast; field_simp; ring
      · simp
  · refine ⟨fun s => ⟨fun o => Matrix.PosSemidef.one.smul hc0, hsum1⟩, 1, fun _ => 1,
      fun _ _ _ => ((a : ℕ) : ℝ)⁻¹, ⟨fun _ => Matrix.PosSemidef.one, by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp⟩, ?_, ?_, ?_⟩
    · intro _ _ _; positivity
    · intro _ _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro _ _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [hc]
  · intro s o
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      smul_eq_mul, hc]
    push_cast
    field_simp
    ring

lemma X7_min {x a d : ℕ+} (M : MeasurementFamily x a d) (hM : ValidMeasurements M) :
    ∃ r : ℝ, ∃ N : MeasurementFamily x a d, ∃ G : (Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ,
      0 ≤ r ∧ ValidMeasurements N ∧ IsPOVM G ∧
      (∀ s o, M s o + (r : ℂ) • N s o = ((1 + r : ℝ) : ℂ) • X7_marg G s o) ∧
      ∀ r' : ℝ, ∀ N' F' : MeasurementFamily x a d, 0 ≤ r' → ValidMeasurements N' →
        CompatiblePOVMs F' → (∀ s o, M s o + (r' : ℂ) • N' s o = ((1 + r' : ℝ) : ℂ) • F' s o) →
        r ≤ r' := by
  obtain ⟨N0, F0, hN0, hF0, h0⟩ := X7_feasible M hM
  obtain ⟨G0, hG0, rfl⟩ := X7_compat_joint hF0
  set r0 : ℝ := ((a : ℕ) : ℝ) with hr0
  have hr00 : 0 ≤ r0 := Nat.cast_nonneg _
  let V : Set (MeasurementFamily x a d) := {N | ∀ s, IsPOVM (N s)}
  have hV : IsCompact V := by
    have : V = Set.univ.pi (fun _ => {P | IsPOVM P}) := by ext; simp [V, Set.mem_pi]
    rw [this]; exact isCompact_univ_pi fun _ => X7_povm_compact
  let W : Set ((Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ) := {G | IsPOVM G}
  have hW : IsCompact W := X7_povm_compact
  let E : Set (ℝ × MeasurementFamily x a d × ((Fin x → Fin a) → Matrix (Fin d) (Fin d) ℂ)) :=
    ⋂ s, ⋂ o, {t | M s o + (t.1 : ℂ) • t.2.1 s o = ((1 + t.1 : ℝ) : ℂ) • X7_marg t.2.2 s o}
  have hE : IsClosed E := by
    apply isClosed_iInter; intro s
    apply isClosed_iInter; intro o
    apply isClosed_eq
    · exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul
        ((continuous_apply o).comp ((continuous_apply s).comp (continuous_fst.comp continuous_snd))))
    · exact (Complex.continuous_ofReal.comp (continuous_const.add continuous_fst)).smul
        (continuous_finset_sum _ fun ω _ => (continuous_apply ω).comp (continuous_snd.comp continuous_snd))
  let K := (Set.Icc 0 r0 ×ˢ V ×ˢ W) ∩ E
  have hK : IsCompact K := (isCompact_Icc.prod (hV.prod hW)).inter_right hE
  have hne : (Prod.fst '' K).Nonempty :=
    ⟨r0, (r0, N0, G0), ⟨⟨⟨hr00, le_rfl⟩, hN0, hG0⟩, by
      simp only [E, Set.mem_iInter, Set.mem_setOf_eq]; exact h0⟩, rfl⟩
  obtain ⟨_, ⟨⟨r, N, G⟩, ⟨⟨hr, hN, hG⟩, hEq⟩, rfl⟩, hleast⟩ :=
    (hK.image continuous_fst).exists_isLeast hne
  refine ⟨r, N, G, hr.1, hN, hG, by simpa [E] using hEq, ?_⟩
  intro r' N' F' h0' hN' hF' heq'
  by_cases hle : r' ≤ r0
  · obtain ⟨G', hG', rfl⟩ := X7_compat_joint hF'
    exact hleast ⟨(r', N', G'), ⟨⟨⟨h0', hle⟩, hN', hG'⟩, by
      simp only [E, Set.mem_iInter, Set.mem_setOf_eq]; exact heq'⟩, rfl⟩
  · exact le_trans hr.2 (le_of_lt (not_le.mp hle))

end QAlgorithms.Papers.Independent.Dependency50.P32.X7B12M

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P32
  QAlgorithms.Papers.Independent.Dependency50.P32.X7B12M in
open QAlgorithms.Papers.Independent.Information100.P07 (support) in
theorem solution (O : ResourceTheory) {x a d : ℕ+}
    (hallowed : O.allowed (measurementPort x a d) =
      {J | ∃ M : MeasurementFamily x a d, ValidMeasurements M ∧ J = measurementChoi M})
    (hfree : O.free (measurementPort x a d) =
      {J | ∃ M : MeasurementFamily x a d, CompatiblePOVMs M ∧ J = measurementChoi M})
    (M : MeasurementFamily x a d) (hM : ValidMeasurements M) :
    incompatibility M = maximal O (measurementChoi M) ∧
    IsLeast (measurementValues M) (incompatibility M) ∧
    ∃ r : ℝ, 0 ≤ r ∧ ENNReal.ofReal (1 + r) = incompatibility M ∧
      ∃ N F : MeasurementFamily x a d, ValidMeasurements N ∧ CompatiblePOVMs F ∧
        (∀ s o, M s o + (r : ℂ) • N s o = ((1 + r : ℝ) : ℂ) • F s o) ∧
        measurementChoi N ∈ O.allowed (measurementPort x a d) ∧
        measurementChoi F ∈ O.free (measurementPort x a d) ∧
        measurementChoi M + (r : ℂ) • measurementChoi N =
          ((1 + r : ℝ) : ℂ) • measurementChoi F := by
  obtain ⟨r, N, G, hr, hN, hG, heq, hleast⟩ := X7_min M hM
  have hL : IsLeast (measurementValues M) (ENNReal.ofReal (1 + r)) := by
    refine ⟨⟨r, hr, rfl, N, X7_marg G, hN, X7_marg_compat hG, heq⟩, ?_⟩
    rintro z ⟨r', hr', rfl, N', F', hN', hF', heq'⟩
    exact ENNReal.ofReal_le_ofReal (by linarith [hleast r' N' F' hr' hN' hF' heq'])
  have hinc : incompatibility M = ENNReal.ofReal (1 + r) := hL.csInf_eq
  refine ⟨?_, hinc ▸ hL, r, hr, hinc.symm, N, X7_marg G, hN, X7_marg_compat hG, heq, ?_, ?_, ?_⟩
  · unfold incompatibility maximal robustness
    congr 1
    ext z
    constructor
    · rintro ⟨r', hr', hz, N', F', hN', hF', heq'⟩
      refine ⟨r', hr', hz, measurementChoi N', ?_, measurementChoi F', ?_,
        (X7_mc_eq_iff M N' F' r').2 heq'⟩
      · rw [hallowed]; exact ⟨N', hN', rfl⟩
      · rw [hfree]; exact ⟨F', hF', rfl⟩
    · rintro ⟨r', hr', hz, J, hJ, Jf, hJf, heq'⟩
      rw [hallowed] at hJ
      rw [hfree] at hJf
      obtain ⟨N', hN', rfl⟩ := hJ
      obtain ⟨F', hF', rfl⟩ := hJf
      exact ⟨r', hr', hz, N', F', hN', hF', (X7_mc_eq_iff M N' F' r').1 heq'⟩
  · rw [hallowed]; exact ⟨N, hN, rfl⟩
  · rw [hfree]; exact ⟨X7_marg G, X7_marg_compat hG, rfl⟩
  · exact (X7_mc_eq_iff M N (X7_marg G) r).2 heq
