-- Prove2me | solution 1 for StrongConv.exists_uniformExp_trN_wordEval_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:46:03.740251+00:00
-- url     : https://prove2.me/submissions/f1111635-39db-4f14-8026-9dc2b07bbb29

import Mathlib
import Definitions.Def_StrongConv
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card


end StrongConv.S5
end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartRoot

open FreeGroup FreeGroup.reduceCyclically

end StrongConv.S5.PartRoot

end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem trN_wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    trN N (wordEval (sModel σ) w) = ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trN]
  rw [trN, wordEval_sModel, trace_permOpPerp hN]
  simp

/-! ### The left-regular representation -/

end StrongConv.S5.PartPerm


end
section

open Polynomial Finset

noncomputable section

namespace StrongConv.S5.PartAlg

/-- The linear factor `1 - j X`. -/
abbrev L (j : ℕ) : ℝ[X] := 1 - (j : ℝ[X]) * X

lemma L_eq (j : ℕ) : L j = C (-(j : ℝ)) * X + C 1 := by
  simp [L, sub_eq_add_neg, add_comm, map_natCast]

lemma natDegree_L (j : ℕ) (hj : 1 ≤ j) : (L j).natDegree = 1 := by
  rw [L_eq]
  apply natDegree_linear
  have : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  simpa using this

lemma natDegree_L_le (j : ℕ) : (L j).natDegree ≤ 1 := by
  rw [L_eq]; exact natDegree_linear_le

lemma eval_L (j : ℕ) (x : ℝ) : (L j).eval x = 1 - j * x := by
  simp [L]

lemma natDegree_gPoly (d q : ℕ) :
    (gPoly d q).natDegree = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
  unfold gPoly
  rw [natDegree_prod]
  · apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    rw [natDegree_pow, natDegree_L j hj.1, mul_one]
  · intro j hj
    rw [mem_Ico] at hj
    apply pow_ne_zero
    intro h
    have := natDegree_L j hj.1
    change L j = 0 at h
    rw [h] at this; simp at this

lemma factor_pos (j q N : ℕ) (hj : j < q) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    0 < 1 - (j : ℝ) * (1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : (j : ℝ) < N := by exact_mod_cast (by omega : j < N)
  rw [mul_one_div, sub_pos, div_lt_one hNpos]
  exact this

lemma eval_prod_pos (q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) (s : Finset ℕ) (hs : ∀ j ∈ s, j < q)
    (k : ℕ → ℕ) : 0 < (∏ j ∈ s, L j ^ k j).eval (1 / (N : ℝ)) := by
  rw [eval_prod]
  apply prod_pos
  intro j hj
  rw [eval_pow, eval_L]
  exact pow_pos (factor_pos j q N (hs j hj) hN hN1) _

theorem gPoly_eval_ne_zero (d q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    (gPoly d q).eval (1 / (N : ℝ)) ≠ 0 := by
  have := eval_prod_pos q N hN hN1 (Ico 1 q) (fun j hj => (mem_Ico.1 hj).2)
    (fun j => min d (q / (j + 1)))
  exact ne_of_gt this

lemma descFactorial_eq (N m : ℕ) (hN1 : 1 ≤ N) :
    (N.descFactorial m : ℝ) = (N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Nat.descFactorial_succ, prod_Ico_succ_top (by omega : 1 ≤ m), Nat.cast_mul]
    by_cases hmN : m ≤ N
    · rw [Nat.cast_sub hmN, ih]
      field_simp
      ring
    · have h0 : N.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      have hih : (N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))) = 0 := by
        rw [← ih, h0]; simp
      rw [h0]
      simp only [Nat.cast_zero, mul_zero]
      calc (0 : ℝ) = (N : ℝ) * ((N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))))
            * (1 - (m : ℝ) * (1 / (N : ℝ))) := by rw [hih]; ring
        _ = _ := by ring

lemma filter_lt_Ico (e q : ℕ) (he : e ≤ q) : (Ico 1 q).filter (· < e) = Ico 1 e := by
  ext j; simp only [mem_filter, mem_Ico]; omega

lemma prod_prod_Ico {d : ℕ} (e : Fin d → ℕ) (q : ℕ) (he : ∀ i, e i ≤ q) (f : ℕ → ℝ) :
    ∏ i, ∏ j ∈ Ico 1 (e i), f j =
      ∏ j ∈ Ico 1 q, f j ^ (univ.filter (fun i => j < e i)).card := by
  have : ∀ i, ∏ j ∈ Ico 1 (e i), f j = ∏ j ∈ Ico 1 q, (if j < e i then f j else 1) := by
    intro i
    rw [← prod_filter, filter_lt_Ico _ _ (he i)]
  simp_rw [this]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro j _
  rw [← prod_filter, prod_const]

theorem exists_poly_term (d q : ℕ) (hq : 1 ≤ q) (p : ℕ × (Fin d → ℕ)) (h1 : 1 ≤ p.1)
    (h2 : p.1 ≤ ∑ i, p.2 i + 1) (h3 : ∑ i, p.2 i ≤ q) :
    ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d q).natDegree + min d q ∧
      ∀ N : ℕ, q ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) * ((N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)) =
          φ.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  obtain ⟨v, e⟩ := p
  simp only at h1 h2 h3 ⊢
  set E := ∑ i, e i with hE
  have he : ∀ i, e i ≤ q := fun i =>
    le_trans (single_le_sum (fun i _ => Nat.zero_le (e i)) (mem_univ i)) h3
  set c : ℕ → ℕ := fun j => (univ.filter (fun i => j < e i)).card with hc
  set dd : ℕ → ℕ := fun j => min d (q / (j + 1)) with hdd
  have hcd : ∀ j, c j ≤ dd j := by
    intro j
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc c j * (j + 1) = ∑ i ∈ univ.filter (fun i => j < e i), (j + 1) := by
            simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => j < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  -- Σ_{j<q} c j = E
  have hsumc : ∑ j ∈ range q, c j = E := by
    simp only [hc, card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (range q).filter (fun j => j < e i) = range (e i) := by
      ext j; simp only [mem_filter, mem_range]; have := he i; omega
    rw [this, card_range]
  have hc0 : c 0 ≤ min d q := by
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · calc c 0 = ∑ i ∈ univ.filter (fun i => 0 < e i), 1 := by simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => 0 < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  have hsplit : ∑ j ∈ range q, c j = c 0 + ∑ j ∈ Ico 1 q, c j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  refine ⟨X ^ (E + 1 - v) * (∏ j ∈ Ico 1 v, L j) * ∏ j ∈ Ico 1 q, L j ^ (dd j - c j), ?_, ?_⟩
  · rw [natDegree_gPoly]
    have hA : (∏ j ∈ Ico 1 v, L j).natDegree ≤ v - 1 := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ Ico 1 v, (L j).natDegree ≤ ∑ j ∈ Ico 1 v, 1 :=
            sum_le_sum (fun j _ => natDegree_L_le j)
        _ = v - 1 := by simp
    have hR : (∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).natDegree ≤ ∑ j ∈ Ico 1 q, (dd j - c j) := by
      refine (natDegree_prod_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      refine natDegree_pow_le.trans ?_
      calc (dd j - c j) * (L j).natDegree ≤ (dd j - c j) * 1 :=
            Nat.mul_le_mul_left _ (natDegree_L_le j)
        _ = _ := mul_one _
    have hX : (X ^ (E + 1 - v) : ℝ[X]).natDegree ≤ E + 1 - v := natDegree_X_pow_le _
    have hsub : ∑ j ∈ Ico 1 q, (dd j - c j) + ∑ j ∈ Ico 1 q, c j = ∑ j ∈ Ico 1 q, dd j := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _; have := hcd j; omega
    refine (natDegree_mul_le).trans ?_
    have := (natDegree_mul_le (p := (X ^ (E + 1 - v) : ℝ[X])) (q := ∏ j ∈ Ico 1 v, L j))
    have hdd : ∑ j ∈ Ico 1 q, dd j = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := rfl
    omega
  · intro N hN hN1
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    set x : ℝ := 1 / (N : ℝ) with hx
    have hxN : x * N = 1 := by rw [hx]; field_simp
    -- denominators
    have hden : ∏ i, (N.descFactorial (e i) : ℝ) =
        (N : ℝ) ^ E * ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      simp_rw [descFactorial_eq N _ hN1]
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_prod_Ico e q he]
    have hCpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hRpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hg : (gPoly d q).eval x = (∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      unfold gPoly
      rw [eval_prod, ← prod_mul_distrib]
      apply prod_congr rfl
      intro j _
      rw [← pow_add, eval_pow]
      change (L j).eval x ^ _ = _
      rw [eval_L]
      congr 1
      have := hcd j
      simp only [hdd] at this ⊢
      omega
    have hφ : (X ^ (E + 1 - v) * (∏ j ∈ Ico 1 v, L j) *
        ∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).eval x =
        x ^ (E + 1 - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      simp [eval_prod]
    rw [hφ, hg, hden, descFactorial_eq N v hN1]
    have hpow : x * (N : ℝ) ^ v = x ^ (E + 1 - v) * (N : ℝ) ^ E := by
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      obtain ⟨k, hk⟩ : ∃ k, E = k + v' := ⟨E - v', by omega⟩
      rw [hk, show k + v' + 1 - (v' + 1) = k by omega]
      calc x * (N : ℝ) ^ (v' + 1) = (x * N) * (N : ℝ) ^ v' := by ring
        _ = (x * N) ^ k * (N : ℝ) ^ v' := by rw [hxN]; simp
        _ = _ := by ring
    rw [← hx, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    calc x * ((N : ℝ) ^ v * ∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ((∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
            ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j))
        = (x * (N : ℝ) ^ v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ((∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
            ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j)) := by ring
      _ = _ := by rw [hpow]; ring

/-- `#{j < d : (j+1) b ≤ q} = min d (q / b)`. -/
lemma card_filter_mul_le (d b q : ℕ) (hb : 0 < b) :
    ((range d).filter (fun j => (j + 1) * b ≤ q)).card = min d (q / b) := by
  have : (range d).filter (fun j => (j + 1) * b ≤ q) = range (min d (q / b)) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
    rw [← Nat.le_div_iff_mul_le hb]
    omega
  rw [this, card_range]

theorem natDegree_gPoly_add_min_le (d q : ℕ) (hq : 1 ≤ q) :
    (((gPoly d q).natDegree + min d q : ℕ) : ℝ) ≤ q * (1 + Real.log d) := by
  have key : (gPoly d q).natDegree + min d q = ∑ j ∈ range d, q / (j + 1) := by
    rw [natDegree_gPoly]
    have h1 : ∑ m ∈ range q, min d (q / (m + 1)) =
        min d q + ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
      simp
    rw [add_comm, ← h1]
    have h2 : ∀ m, min d (q / (m + 1)) =
        ∑ j ∈ range d, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro m
      rw [← card_filter_mul_le d (m + 1) q (by omega), card_filter]
    have h3 : ∀ j, q / (j + 1) =
        ∑ m ∈ range q, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro j
      have := card_filter_mul_le q (j + 1) q (by omega)
      rw [min_eq_right (Nat.div_le_self _ _), card_filter] at this
      rw [← this]
      apply sum_congr rfl; intro m _; rw [mul_comm]
    simp_rw [h2, h3]
    rw [sum_comm]
  rw [key]
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc ((∑ j ∈ range d, q / (j + 1) : ℕ) : ℝ) ≤ ∑ j ∈ range d, (q : ℝ) / ((j : ℝ) + 1) := by
        push_cast
        apply sum_le_sum; intro j _
        have := Nat.cast_div_le (α := ℝ) (m := q) (n := j + 1)
        push_cast at this
        exact this
    _ = q * (harmonic d : ℝ) := by
        simp only [harmonic]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro j _
        field_simp
    _ ≤ q * (1 + Real.log d) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) hq0

end StrongConv.S5.PartAlg

end
section

/-!
# Part Comb: the expected number of fixed points of a random word permutation

Proof of `StrongConv.S5.exists_fixCount_expectation` (stated in `Blueprint.lean`).
-/

open Finset

noncomputable section

namespace StrongConv.S5.PartComb

open StrongConv StrongConv.S5

/-! ## Counting permutations extending a partial injection -/

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext (E : Finset (α × α)) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      if PInj E then (Fintype.card α - E.card).factorial else 0 := by
  split_ifs with h
  · obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
    have hA : (E.image Prod.fst).card = E.card :=
      card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
    rw [← hA, ← card_stab]
    refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
      intro a ha
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
      rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
      simp
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro p hp
      rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
    · intro τ _; simp
    · intro π _; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    apply h
    intro p hp q hq
    constructor
    · intro e; rw [← hτ p hp, ← hτ q hq, e]
    · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end Count

/-! ## Paths along a word -/

section Word

variable {d : ℕ} (w : List (Letter d))

/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

lemma edge_cases {α : Type*} (l : Letter d) (a b : α) :
    ((edge l a b).1 = a ∧ (edge l a b).2 = b) ∨ ((edge l a b).1 = b ∧ (edge l a b).2 = a) := by
  rcases l with _ | i | i <;> simp [edge]

lemma edge_map {α β : Type*} (φ : β → α) (l : Letter d) (a b : β) :
    edge l (φ a) (φ b) = Prod.map φ φ (edge l a b) := by
  rcases l with _ | i | i <;> simp [edge]

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

/-- The path of `y` under `σ`. -/
def path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) : Fin (w.length + 1) → Fin N :=
  fun t => wordPerm σ (w.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Letter d)
    (ws : List (Letter d)) (y : Fin N) :
    wordPerm σ (l :: ws) y = letterPerm σ l (wordPerm σ ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y 0 = wordPerm σ w y := by
  simp [path]

lemma path_step {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) (t : Fin w.length) :
    path w σ y t.castSucc = letterPerm σ (w.get t) (path w σ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N)
    (hx : Rz w σ x) : x = path w σ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    fixCount (wordPerm σ w) =
      (univ.filter fun x : Fin (w.length + 1) → Fin N => Rz w σ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path w σ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path w σ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step w σ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path w σ x hx.1).symm
  · intro y _
    exact path_last w σ y

lemma Rz_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Rz w σ x ↔ Cons w x ∧ ∀ i, ∀ p ∈ Es w x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun t ht => by have := h t; rw [ht] at this; simpa [letterPerm] using this, ?_⟩
    intro i p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [mem_filter] at ht
    have h' := h t
    generalize w.get t = l at ht h'
    rcases l with _ | j | j
    · simp [lab] at ht
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge]; exact h'.symm
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge, letterPerm] at h' ⊢
      rw [h']; simp
  · rintro ⟨hc, he⟩ t
    have hmem : ∀ j, lab (w.get t) = some j →
        edge (w.get t) (x t.castSucc) (x t.succ) ∈ Es w x j := fun j hj =>
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hj⟩, rfl⟩
    have hct := hc t
    generalize w.get t = l at hmem hct
    rcases l with _ | j | j
    · simp [letterPerm, hct rfl]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, this]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, ← this]

lemma card_Rz {N : ℕ} (x : Fin (w.length + 1) → Fin N) :
    (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => Rz w σ x).card =
      if Cons w x then
        ∏ i, (if PInj (Es w x i) then (N - (Es w x i).card).factorial else 0)
      else 0 := by
  split_ifs with hc
  · have : (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => Rz w σ x) =
        Fintype.piFinset (fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
          ∀ p ∈ Es w x i, τ p.1 = p.2) := by
      ext σ; simp [Rz_iff, hc, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_ext, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    exact hc ((Rz_iff w σ x).1 h).1

/-- The weight of a path. -/
def G (N : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : ℕ :=
  if Good w x then ∏ i, (N - (Es w x i).card).factorial else 0

lemma sum_fixCount (N : ℕ) :
    ∑ σ : Fin d → Equiv.Perm (Fin N), fixCount (wordPerm σ w) =
      ∑ x : Fin (w.length + 1) → Fin N, G w N x := by
  simp only [fixCount_eq, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  by_cases hcl : x 0 = x (Fin.last _)
  · simp only [hcl, and_true]
    rw [card_Rz, G]
    by_cases hg : Good w x
    · rw [if_pos hg, if_pos hg.1]
      exact prod_congr rfl fun i _ => if_pos (hg.2.1 i)
    · rw [if_neg hg]
      split_ifs with hc
      · have : ¬ ∀ i, PInj (Es w x i) := fun h => hg ⟨hc, h, hcl⟩
        push Not at this
        obtain ⟨i, hi⟩ := this
        exact prod_eq_zero (mem_univ i) (if_neg hi)
      · rfl
  · simp only [hcl, and_false, G]
    rw [if_neg (fun h => hcl h.2.2)]
    simp

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The first position where `x` takes the value `x t`. -/
def canon (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

/-- The number of values of a path. -/
def nv (x : Fin n → α) : ℕ := (univ.image x).card

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [Fintype β] in
lemma Es_comp (c : Fin (w.length + 1) → β) (φ : β → α) (i : Fin d) :
    Es w (φ ∘ c) i = (Es w c i).image (Prod.map φ φ) := by
  simp only [Es, image_image]
  refine image_congr fun t _ => ?_
  simp [edge_map]

omit [Fintype β] in
lemma Es_range (c : Fin (w.length + 1) → β) (i : Fin d) (p : β × β) (hp : p ∈ Es w c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  rcases edge_cases (w.get t) (c t.castSucc) (c t.succ) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

omit [Fintype α] [Fintype β] in
lemma card_Es_comp (i : Fin d) : (Es w (φ ∘ c) i).card = (Es w c i).card := by
  rw [Es_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := Es_range w c i p hp
  have hq' := Es_range w c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

lemma good_comp : Good w (φ ∘ c) ↔ Good w c := by
  have key : ∀ s t, φ (c s) = φ (c t) ↔ c s = c t := fun s t =>
    hφ.eq_iff ⟨s, rfl⟩ ⟨t, rfl⟩
  have hP : ∀ i, PInj (Es w (φ ∘ c) i) ↔ PInj (Es w c i) := by
    intro i
    rw [Es_comp]
    unfold PInj
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
      Prod.map_snd]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    have hp' := Es_range w c i p hp
    have hq' := Es_range w c i q hq
    rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]
  unfold Good Cons
  simp only [Function.comp, key, hP]

lemma G_comp (N : ℕ) : G w N (φ ∘ c) = G w N c := by
  unfold G
  simp only [good_comp w c φ hφ, card_Es_comp w c φ hφ]

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

lemma sum_card_Es_le (x : Fin (w.length + 1) → α) : ∑ i, (Es w x i).card ≤ w.length := by
  calc ∑ i, (Es w x i).card
      ≤ ∑ i, (univ.filter fun t : Fin w.length => lab (w.get t) = some i).card :=
        sum_le_sum fun i _ => card_image_le
    _ = (univ.biUnion fun i => univ.filter fun t : Fin w.length => lab (w.get t) = some i).card := by
        rw [card_biUnion]
        intro i _ j _ hij
        show Disjoint _ _
        rw [disjoint_filter]
        intro t _ hi hj
        exact hij (Option.some.inj (hi.symm.trans hj))
    _ ≤ w.length := (card_le_univ _).trans (Fintype.card_fin _).le

/-- The values of a path at positions `≤ k`. -/
def U (x : Fin (w.length + 1) → α) (k : ℕ) : Finset α :=
  (univ.filter fun t : Fin (w.length + 1) => t.val ≤ k).image x

/-- The edges of a path at steps `< k`. -/
def Ed (x : Fin (w.length + 1) → α) (k : ℕ) : Finset (α × α) :=
  (univ.filter fun t : Fin w.length => t.val < k ∧ lab (w.get t) ≠ none).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

lemma Ed_mem_U (x : Fin (w.length + 1) → α) (k : ℕ) (p : α × α) (hp : p ∈ Ed w x k) :
    p.1 ∈ U w x k ∧ p.2 ∈ U w x k := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
  have hs := (mem_filter.1 hs).2.1
  have h1 : x s.castSucc ∈ U w x k :=
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)
  have h2 : x s.succ ∈ U w x k :=
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)
  rcases edge_cases (w.get s) (x s.castSucc) (x s.succ) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2]
  exacts [⟨h1, h2⟩, ⟨h2, h1⟩]

lemma U_Ed (x : Fin (w.length + 1) → α) (hc : Cons w x) :
    ∀ k, k ≤ w.length → (U w x k).card ≤ (Ed w x k).card + 1
  | 0, _ => by
      have : U w x 0 ⊆ {x 0} := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := mem_image.1 ha
        have : t = 0 := Fin.ext (by have := (mem_filter.1 ht).2; simp only [Fin.val_zero]; omega)
        simp [this]
      calc (U w x 0).card ≤ ({x 0} : Finset α).card := card_le_card this
        _ = 1 := card_singleton _
        _ ≤ _ := by omega
  | k + 1, hk => by
      have ih := U_Ed x hc k (by omega)
      let t : Fin w.length := ⟨k, by omega⟩
      have hU : U w x (k + 1) ⊆ insert (x t.succ) (U w x k) := by
        intro a ha
        obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
        have hs := (mem_filter.1 hs).2
        rcases Nat.lt_or_ge s.val (k + 1) with h | h
        · exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega⟩))
        · have : s = t.succ := Fin.ext (by simp [t]; omega)
          rw [this]; exact mem_insert_self _ _
      have hE : Ed w x k ⊆ Ed w x (k + 1) := by
        intro p hp
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
        have hs := (mem_filter.1 hs).2
        exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega, hs.2⟩)
      by_cases hmem : x t.succ ∈ U w x k
      · calc (U w x (k + 1)).card ≤ (insert (x t.succ) (U w x k)).card := card_le_card hU
          _ = (U w x k).card := by rw [insert_eq_of_mem hmem]
          _ ≤ (Ed w x k).card + 1 := ih
          _ ≤ (Ed w x (k + 1)).card + 1 := by have := card_le_card hE; omega
      · have hcs : x t.castSucc ∈ U w x k :=
          mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp [t]⟩)
        have hl : lab (w.get t) ≠ none := by
          intro hl
          apply hmem
          have hnone : w.get t = none := by
            generalize w.get t = l at hl
            rcases l with _ | j | j <;> simp_all [lab]
          rw [← hc t hnone]; exact hcs
        set e := edge (w.get t) (x t.castSucc) (x t.succ) with he
        have hnew : e ∉ Ed w x k := by
          intro h
          have := Ed_mem_U w x k e h
          rcases edge_cases (w.get t) (x t.castSucc) (x t.succ) with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [← he] at e2; rw [e2] at this; exact hmem this.2
          · rw [← he] at e1; rw [e1] at this; exact hmem this.1
        have hsub : insert e (Ed w x k) ⊆ Ed w x (k + 1) := by
          refine insert_subset ?_ hE
          exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp [t], hl⟩)
        have h3 := card_le_card hsub
        rw [card_insert_of_notMem hnew] at h3
        have h4 := card_le_card hU
        have h5 := card_insert_le (x t.succ) (U w x k)
        omega

lemma nv_le (x : Fin (w.length + 1) → α) (hc : Cons w x) :
    nv x ≤ ∑ i, (Es w x i).card + 1 := by
  have h1 : nv x = (U w x w.length).card := by
    unfold nv U
    congr 1
    rw [filter_true_of_mem fun t _ => Nat.lt_succ_iff.1 t.2]
  have h2 : Ed w x w.length ⊆ univ.biUnion (Es w x) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (mem_filter.1 ht).2.2
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hi⟩)⟩
  have h3 := U_Ed w x hc w.length le_rfl
  have h4 := (card_le_card h2).trans card_biUnion_le
  omega

end Bounds

theorem exists_fixCount_expectation (d : ℕ) (w : List (Letter d)) :
    ∃ M : Multiset (ℕ × (Fin d → ℕ)),
      (∀ p ∈ M, 1 ≤ p.1 ∧ p.1 ≤ ∑ i, p.2 i + 1 ∧ ∑ i, p.2 i ≤ w.length) ∧
      ∀ N : ℕ, 1 ≤ N → w.length ≤ N →
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => (fixCount (wordPerm σ w) : ℝ)) =
          (M.map fun p => (N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)).sum := by
  let C : Finset (Fin (w.length + 1) → Fin (w.length + 1)) :=
    (univ.filter fun c => canon c = c).filter (Good w)
  refine ⟨C.val.map fun c => (nv c, fun i => (Es w c i).card), ?_, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hp
    have hc := (mem_filter.1 hc).2
    exact ⟨show 0 < nv c from card_pos.2 (univ_nonempty.image c), nv_le w c hc.1,
      sum_card_Es_le w c⟩
  · intro N _ hL
    have h1 : ∑ σ : Fin d → Equiv.Perm (Fin N), fixCount (wordPerm σ w) =
        ∑ c ∈ (univ.filter fun c : Fin (w.length + 1) → Fin (w.length + 1) => canon c = c),
          if Good w c then N.descFactorial (nv c) * ∏ i, (N - (Es w c i).card).factorial
          else 0 := by
      rw [sum_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
        (t := univ.filter fun c : Fin (w.length + 1) → Fin (w.length + 1) => canon c = c)
        (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
      refine sum_congr rfl fun c hc => ?_
      have hc := (mem_filter.1 hc).2
      have hG : ∀ x ∈ univ.filter fun x : Fin (w.length + 1) → Fin N => canon x = c,
          G w N x = G w N c := by
        intro x hx
        have hx := (mem_filter.1 hx).2
        rw [← hx]
        conv_lhs => rw [← comp_canon x]
        exact G_comp w (canon x) x (injOn_canon x) N
      rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, smul_eq_mul, G]
      split_ifs <;> simp
    unfold uniformExp
    rw [← Nat.cast_sum, h1, ← sum_filter, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
      simp [Fintype.card_perm]
    rw [hcard, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun c _ => ?_
    have he : ∀ i, (Es w c i).card ≤ N := fun i =>
      (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans
        ((sum_card_Es_le w c).trans hL)
    have hfac : (N.factorial : ℝ) ^ d =
        (∏ i, (N.descFactorial (Es w c i).card : ℝ)) *
          ∏ i, ((N - (Es w c i).card).factorial : ℝ) := by
      rw [← prod_mul_distrib,
        show (N.factorial : ℝ) ^ d = ∏ _i : Fin d, (N.factorial : ℝ) by simp]
      refine prod_congr rfl fun i _ => ?_
      rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
    simp only [Function.comp, Nat.cast_mul, Nat.cast_prod]
    rw [hfac, mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun i _ => by positivity)]

end StrongConv.S5.PartComb

end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

theorem natDegree_multiset_sum_le' {ι : Type*} (M : Multiset ι) (φ : ι → ℝ[X]) (B : ℕ)
    (h : ∀ p ∈ M, (φ p).natDegree ≤ B) : (M.map φ).sum.natDegree ≤ B := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    refine (natDegree_add_le _ _).trans (max_le (h a (Multiset.mem_cons_self _ _)) ?_)
    exact ih fun p hp => h p (Multiset.mem_cons_of_mem hp)

theorem uniformExp_sub_div {X : Type*} [Fintype X] [Nonempty X] (a : X → ℝ) (N : ℝ) :
    uniformExp (fun x => (a x - 1) / N) = (uniformExp a - 1) / N := by
  unfold uniformExp
  have hc : (Fintype.card X : ℝ) ≠ 0 := by positivity
  rw [← Finset.sum_div, Finset.sum_div]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

theorem lemma51 (d q : ℕ) (hq : 1 ≤ q) (w : List (Letter d)) (hw : w.length ≤ q) :
    ((gPoly d q).natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
        ∀ N : ℕ, q ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) =
            f.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  have hdeg := PartAlg.natDegree_gPoly_add_min_le d q hq
  have hg : ((gPoly d q).natDegree : ℝ) ≤ q * (1 + Real.log d) := by
    refine le_trans ?_ hdeg
    exact_mod_cast Nat.le_add_right _ _
  refine ⟨hg, ?_⟩
  obtain ⟨M, hM, hE⟩ := PartComb.exists_fixCount_expectation d w
  have hφ : ∀ p ∈ M, ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d q).natDegree + min d q ∧
      ∀ N : ℕ, q ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) * ((N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)) =
          φ.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hM p hp
    exact PartAlg.exists_poly_term d q hq p h1 h2 (h3.trans hw)
  choose! φ hφdeg hφeq using hφ
  refine ⟨(M.map φ).sum - X * gPoly d q, ?_, ?_⟩
  · have hs := natDegree_multiset_sum_le' M φ _ (fun p hp => hφdeg p hp)
    have hx : (X * gPoly d q).natDegree ≤ (gPoly d q).natDegree + 1 := by
      refine (natDegree_mul_le).trans ?_
      simp [add_comm]
    have hsub := natDegree_sub_le ((M.map φ).sum) (X * gPoly d q)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have hg0 : gPoly 0 q = 1 := by simp [gPoly]
      have hb : ((1 : ℕ) : ℝ) ≤ q * (1 + Real.log (0 : ℕ)) := by simp; exact_mod_cast hq
      have : (((M.map φ).sum - X * gPoly 0 q).natDegree) ≤ 1 := by
        rw [hg0] at hs hx hsub ⊢
        simp at hs hx hsub ⊢
        omega
      calc _ ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast this
        _ ≤ _ := hb
    · have hm : 1 ≤ min d q := le_min hd hq
      refine le_trans ?_ hdeg
      exact_mod_cast (hsub.trans (max_le hs (by omega)))
  · intro N hN
    have hN1 : 1 ≤ N := hq.trans hN
    have hne := PartAlg.gPoly_eval_ne_zero d q N hN hN1
    haveI : Nonempty (Fin d → Equiv.Perm (Fin N)) := ⟨fun _ => 1⟩
    have hfun : (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) =
        fun σ => ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
      funext σ; exact PartPerm.trN_wordEval_sModel σ w
    rw [hfun, uniformExp_sub_div, hE N hN1 (hw.trans hN)]
    rw [eval_sub, eval_mul, eval_X, eval_multisetSum, Multiset.map_map]
    rw [eq_div_iff hne]
    have key : (M.map (eval (1 / (N : ℝ)) ∘ φ)).sum =
        ((M.map fun p => (1 / (N : ℝ)) * ((N.descFactorial p.1 : ℝ) /
          ∏ i, (N.descFactorial (p.2 i) : ℝ))).sum) * (gPoly d q).eval (1 / (N : ℝ)) := by
      rw [← Multiset.sum_map_mul_right]
      congr 1
      refine Multiset.map_congr rfl fun p hp => ?_
      simp only [Function.comp]
      rw [hφeq p hp N hN hN1, div_mul_cancel₀ _ hne]
    rw [key, Multiset.sum_map_mul_left]
    ring

end StrongConv.S5


end

open Polynomial in
theorem solution (d q : ℕ) (hq : 1 ≤ q) (w : List (StrongConv.Letter d))
    (hw : w.length ≤ q) :
    ((StrongConv.gPoly d q).natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ q * (1 + Real.log d) ∧
        ∀ N : ℕ, q ≤ N →
          StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => StrongConv.trN N (StrongConv.wordEval (StrongConv.sModel σ) w)) =
            f.eval (1 / (N : ℝ)) / (StrongConv.gPoly d q).eval (1 / (N : ℝ)) :=
  StrongConv.S5.lemma51 d q hq w hw
