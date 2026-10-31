-- Prove2me | solution 1 for WainwrightHDS.EigPert.max_eigenvector_perturbation_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:49:21.55443+00:00
-- url     : https://prove2.me/submissions/feae44a3-2033-4bbc-8c40-49c76e83b614

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_gamma
import Definitions.Def_WainwrightHDS_EigPert_IsMaxEigenvector
import Definitions.Def_WainwrightHDS_EigPert_ptilde
import Theorems.Thm_WainwrightHDS_EigPert_pca_basic_inequality
import Theorems.Thm_WainwrightHDS_EigPert_abs_psi_le

open WainwrightHDS.EigPert Matrix

theorem exists_maxEigenvector {n : ℕ} (Q : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hQ : Q.IsHermitian) :
    ∃ θhat, IsMaxEigenvector Q hQ θhat := by
  let hT := isSymmetric_toEuclideanLin_iff.mpr hQ
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let i0 : Fin (Fintype.card (Fin (n + 2))) := Fin.cast (Fintype.card_fin (n + 2)).symm 0
  use b i0
  constructor
  · exact b.orthonormal.1 i0
  · have h_ev := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    dsimp [gamma, Matrix.IsHermitian.eigenvalues₀]
    exact h_ev

theorem rayleigh_le_gamma_zero {n : ℕ} (Q : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hQ : Q.IsHermitian)
    (θhat : EuclideanSpace ℝ (Fin (n + 2))) (hθhat : IsMaxEigenvector Q hQ θhat)
    (θ : EuclideanSpace ℝ (Fin (n + 2))) (hθ : ‖θ‖ = 1) :
    inner ℝ θ (toEuclideanLin Q θ) ≤ inner ℝ θhat (toEuclideanLin Q θhat) := by
  have h_hat_val : inner ℝ θhat (toEuclideanLin Q θhat) = gamma Q hQ 0 := by
    rw [hθhat.2, inner_smul_right, real_inner_self_eq_norm_mul_norm, hθhat.1, mul_one, mul_one]
  rw [h_hat_val]
  let hT := isSymmetric_toEuclideanLin_iff.mpr hQ
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = Fintype.card (Fin (n + 2)) := finrank_euclideanSpace
  let b := hT.eigenvectorBasis hn
  have h_inner : inner ℝ θ (toEuclideanLin Q θ) = inner ℝ (b.repr θ) (b.repr (toEuclideanLin Q θ)) := by
    rw [b.repr.inner_map_map]
  have h_repr_T : ∀ i, (b.repr (toEuclideanLin Q θ)).ofLp i = hT.eigenvalues hn i * (b.repr θ).ofLp i := by
    intro i
    exact hT.eigenvectorBasis_apply_self_apply hn θ i
  have h_euc_inner : inner ℝ (b.repr θ) (b.repr (toEuclideanLin Q θ)) =
      ∑ i, hT.eigenvalues hn i * (b.repr θ).ofLp i ^ 2 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_repr_T i, Real.inner_apply]
    ring
  have h_le : (∑ i, hT.eigenvalues hn i * (b.repr θ).ofLp i ^ 2) ≤
      ∑ i, hT.eigenvalues hn 0 * (b.repr θ).ofLp i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have h_anti := hT.eigenvalues_antitone hn (Fin.zero_le i)
    have : 0 ≤ (b.repr θ).ofLp i ^ 2 := sq_nonneg _
    nlinarith
  have h_sum : (∑ i, hT.eigenvalues hn 0 * (b.repr θ).ofLp i ^ 2) =
      hT.eigenvalues hn 0 * ∑ i, (b.repr θ).ofLp i ^ 2 := by
    rw [← Finset.mul_sum]
  have h_norm : (∑ i, (b.repr θ).ofLp i ^ 2) = 1 := by
    have h_norm_repr : ‖b.repr θ‖ ^ 2 = 1 := by
      rw [LinearIsometryEquiv.norm_map, hθ, one_pow]
    rw [PiLp.norm_sq_eq_of_L2] at h_norm_repr
    have h_simp : (∑ i, ‖(b.repr θ).ofLp i‖ ^ 2) = ∑ i, (b.repr θ).ofLp i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_simp] at h_norm_repr
    exact h_norm_repr
  have h_gamma0 : hT.eigenvalues hn 0 = gamma Q hQ 0 := by
    rfl
  rw [h_inner, h_euc_inner]
  refine h_le.trans ?_
  rw [h_sum, h_norm, mul_one, h_gamma0]

theorem opNorm2_conj_orthogonal_le {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    opNorm2 (Uᵀ * P * U) ≤ opNorm2 P := by
  dsimp [opNorm2]
  have hU_star : star U = Uᵀ := rfl
  have hUT_star : star (Uᵀ) = U := by
    rw [← hU_star, star_star]
  have hU_mul : star U * U = 1 := by
    rw [Matrix.mem_orthogonalGroup_iff'] at hU
    exact hU
  have hUT_mul : star (Uᵀ) * Uᵀ = 1 := by
    rw [hUT_star]
    rw [Matrix.mem_orthogonalGroup_iff] at hU
    exact hU
  let TU := toEuclideanCLM (𝕜 := ℝ) (n := Fin n) U
  let TUT := toEuclideanCLM (𝕜 := ℝ) (n := Fin n) Uᵀ
  let TP := toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P
  have hTU_isom : ∀ x, ‖TU x‖ = ‖x‖ := by
    intro x
    have h_sq : ‖TU x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [sq, sq, ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm]
      have : inner ℝ (TU x) (TU x) = inner ℝ ((star TU * TU) x) x := by
        rw [real_inner_comm (TU x) (TU x), ← ContinuousLinearMap.adjoint_inner_right, real_inner_comm x]
        rfl
      rw [this]
      have h1 : star TU * TU = 1 := by
        change star (toEuclideanCLM (𝕜 := ℝ) (n := Fin n) U) * toEuclideanCLM (𝕜 := ℝ) (n := Fin n) U = 1
        rw [← map_star, ← map_mul, hU_mul, map_one]
      rw [h1]
      rfl
    have := sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
    rcases this with h1 | h2
    · exact h1
    · linarith [norm_nonneg (TU x), norm_nonneg x]
  have hTUT_isom : ∀ x, ‖TUT x‖ = ‖x‖ := by
    intro x
    have h_sq : ‖TUT x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [sq, sq, ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm]
      have : inner ℝ (TUT x) (TUT x) = inner ℝ ((star TUT * TUT) x) x := by
        rw [real_inner_comm (TUT x) (TUT x), ← ContinuousLinearMap.adjoint_inner_right, real_inner_comm x]
        rfl
      rw [this]
      have h1 : star TUT * TUT = 1 := by
        change star (toEuclideanCLM (𝕜 := ℝ) (n := Fin n) Uᵀ) * toEuclideanCLM (𝕜 := ℝ) (n := Fin n) Uᵀ = 1
        rw [← map_star, ← map_mul, hUT_mul, map_one]
      rw [h1]
      rfl
    have := sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
    rcases this with h1 | h2
    · exact h1
    · linarith [norm_nonneg (TUT x), norm_nonneg x]
  have h_comp : toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Uᵀ * P * U) = TUT * TP * TU := by
    rw [map_mul, map_mul]
  rw [h_comp]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖TUT (TP (TU x))‖ ≤ ‖TP‖ * ‖x‖
  rw [hTUT_isom]
  have h_le := ContinuousLinearMap.le_opNorm TP (TU x)
  rw [hTU_isom] at h_le
  exact h_le

theorem master_ineq {n : ℕ}
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 2)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (θhat : EuclideanSpace ℝ (Fin (n + 2))) (hθhat : IsMaxEigenvector (S + P) (hS.1.add hP) θhat)
    (hρ : 0 ≤ inner ℝ θhat θstar) :
    (gamma S hS.1 0 - gamma S hS.1 1 - 2 * opNorm2 P) * (1 - (inner ℝ θhat θstar) ^ 2) ≤
      2 * inner ℝ θhat θstar * Real.sqrt (1 - (inner ℝ θhat θstar) ^ 2) * ‖ptilde U P‖ := by
  have h_pca := pca_basic_inequality S hS hgap θstar hθstar P hP
    {v | ‖v‖ = 1} (fun _ h => h) hθstar.1 θhat hθhat.1
    (fun θ hθ => rayleigh_le_gamma_zero (S + P) (hS.1.add hP) θhat hθhat θ hθ)
  have h_abs := abs_psi_le (n := n + 1) U hU θstar (fun i => by
    have := hU0 i
    exact this) P hP θhat hθhat.1 hρ
  have h_op := opNorm2_conj_orthogonal_le U hU P
  have h_le1 : inner ℝ θhat θstar ≤ 1 := by
    have := real_inner_le_norm θhat θstar
    rw [hθhat.1, hθstar.1, mul_one] at this
    exact this
  have h_sq_nonneg : 0 ≤ 1 - (inner ℝ θhat θstar) ^ 2 := by
    nlinarith
  have h_op_term : 2 * (1 - (inner ℝ θhat θstar) ^ 2) * opNorm2 (Uᵀ * P * U) ≤
      2 * (1 - (inner ℝ θhat θstar) ^ 2) * opNorm2 P := by
    nlinarith
  linarith

theorem inner_ne_zero_of_isMaxEigenvector {n : ℕ}
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 2)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (hsmall : opNorm2 P < (gamma S hS.1 0 - gamma S hS.1 1) / 2)
    (u : EuclideanSpace ℝ (Fin (n + 2))) (hu : IsMaxEigenvector (S + P) (hS.1.add hP) u) :
    inner ℝ u θstar ≠ 0 := by
  intro h0
  have h_m := master_ineq S hS θstar hθstar hgap U hU hU0 P hP u hu (by linarith)
  rw [h0] at h_m
  ring_nf at h_m
  linarith

theorem max_eigenvector_unique_up_to_sign {n : ℕ}
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 2)) ℝ)
    (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (hsmall : opNorm2 P < (gamma S hS.1 0 - gamma S hS.1 1) / 2)
    (v w : EuclideanSpace ℝ (Fin (n + 2)))
    (hv : IsMaxEigenvector (S + P) (hS.1.add hP) v)
    (hw : IsMaxEigenvector (S + P) (hS.1.add hP) w) :
    v = w ∨ v = -w := by
  have hav_ne : inner ℝ v θstar ≠ 0 :=
    inner_ne_zero_of_isMaxEigenvector S hS θstar hθstar hgap U hU hU0 P hP hsmall v hv
  have haw_ne : inner ℝ w θstar ≠ 0 :=
    inner_ne_zero_of_isMaxEigenvector S hS θstar hθstar hgap U hU hU0 P hP hsmall w hw
  let av := inner ℝ v θstar
  let aw := inner ℝ w θstar
  let u0 := aw • v - av • w
  have hu0_inner : inner ℝ u0 θstar = 0 := by
    dsimp [u0, av, aw]
    rw [inner_sub_left, inner_smul_left, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have hu0_lin : toEuclideanLin (S + P) u0 = gamma (S + P) (hS.1.add hP) 0 • u0 := by
    dsimp [u0]
    rw [map_sub, map_smul, map_smul, hv.2, hw.2]
    rw [smul_comm aw, smul_comm av, ← smul_sub]
  have hu0_zero : u0 = 0 := by
    by_contra h_ne
    have h_norm_pos : 0 < ‖u0‖ := norm_pos_iff.mpr h_ne
    let u := ‖u0‖⁻¹ • u0
    have hu_unit : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h_norm_pos, inv_mul_cancel₀ (ne_of_gt h_norm_pos)]
    have hu_eig : toEuclideanLin (S + P) u = gamma (S + P) (hS.1.add hP) 0 • u := by
      dsimp [u]
      rw [map_smul, hu0_lin, smul_comm]
    have hu_max : IsMaxEigenvector (S + P) (hS.1.add hP) u := ⟨hu_unit, hu_eig⟩
    have hu_inner : inner ℝ u θstar = 0 := by
      dsimp [u]
      rw [inner_smul_left, hu0_inner, mul_zero]
    exact inner_ne_zero_of_isMaxEigenvector S hS θstar hθstar hgap U hU hU0 P hP hsmall u hu_max hu_inner
  have h_smul_eq : aw • v = av • w := sub_eq_zero.mp hu0_zero
  have h_norm_eq : ‖aw • v‖ = ‖av • w‖ := by rw [h_smul_eq]
  rw [norm_smul, norm_smul, hv.1, hw.1, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at h_norm_eq
  have h_cases : aw = av ∨ aw = -av := by
    exact abs_eq_abs.mp h_norm_eq
  rcases h_cases with h_eq | h_neg
  · left
    rw [h_eq] at h_smul_eq
    have : av⁻¹ • (av • v) = av⁻¹ • (av • w) := by rw [h_smul_eq]
    rw [inv_smul_smul₀ hav_ne, inv_smul_smul₀ hav_ne] at this
    exact this
  · right
    have h1 : av • (-v) = av • w := by
      calc av • (-v) = -(av • v) := by rw [smul_neg]
      _ = (-av) • v := by rw [neg_smul]
      _ = aw • v := by rw [h_neg]
      _ = av • w := h_smul_eq
    have : av⁻¹ • (av • (-v)) = av⁻¹ • (av • w) := by rw [h1]
    rw [inv_smul_smul₀ hav_ne, inv_smul_smul₀ hav_ne] at this
    rw [← this, neg_neg]

lemma pert_bound_of_master {ν op ρ D L : ℝ}
    (hν : 0 < ν - 2 * op)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hD_sq : D ^ 2 = 2 * (1 - ρ))
    (hD_nonneg : 0 ≤ D)
    (hL_nonneg : 0 ≤ L)
    (hmaster : (ν - 2 * op) * (1 - ρ ^ 2) ≤ 2 * ρ * Real.sqrt (1 - ρ ^ 2) * L) :
    D ≤ 2 * L / (ν - 2 * op) := by
  by_cases hρ_zero : ρ = 0
  · subst hρ_zero
    have : (ν - 2 * op) * (1 - 0 ^ 2) ≤ 0 := by
      linarith [hmaster]
    linarith
  have hρ_pos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρ_zero)
  by_cases hρ_one : ρ = 1
  · subst hρ_one
    have : D = 0 := by
      nlinarith [hD_sq, hD_nonneg]
    rw [this]
    exact div_nonneg (by linarith) (by linarith)
  have hρ_lt1 : ρ < 1 := lt_of_le_of_ne hρ1 hρ_one
  have h1_sub_ρ2_pos : 0 < 1 - ρ ^ 2 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.mpr h1_sub_ρ2_pos
  have h_diff : 0 ≤ (1 - ρ ^ 2) - (ρ * D) ^ 2 := by
    have : (1 - ρ ^ 2) - (ρ * D) ^ 2 = (1 - ρ) ^ 2 * (1 + 2 * ρ) := by
      calc
        (1 - ρ ^ 2) - (ρ * D) ^ 2 = (1 - ρ ^ 2) - ρ ^ 2 * D ^ 2 := by ring
        _ = (1 - ρ ^ 2) - ρ ^ 2 * (2 * (1 - ρ)) := by rw [hD_sq]
        _ = (1 - ρ) ^ 2 * (1 + 2 * ρ) := by ring
    rw [this]
    have : 0 ≤ (1 - ρ) ^ 2 := sq_nonneg _
    have : 0 ≤ 1 + 2 * ρ := by linarith
    positivity
  have h_rho_D_le_sqrt : ρ * D ≤ Real.sqrt (1 - ρ ^ 2) := by
    have h_sq_le : (ρ * D) ^ 2 ≤ 1 - ρ ^ 2 := by linarith [h_diff]
    exact Real.le_sqrt_of_sq_le h_sq_le
  have h_chain : (ν - 2 * op) * (ρ * D) * Real.sqrt (1 - ρ ^ 2) ≤
      (ν - 2 * op) * (1 - ρ ^ 2) := by
    have : (ν - 2 * op) * (ρ * D) * Real.sqrt (1 - ρ ^ 2) =
        (ν - 2 * op) * ((ρ * D) * Real.sqrt (1 - ρ ^ 2)) := by ring
    rw [this]
    have h_mul_le : (ρ * D) * Real.sqrt (1 - ρ ^ 2) ≤ 1 - ρ ^ 2 := by
      calc
        (ρ * D) * Real.sqrt (1 - ρ ^ 2) ≤ Real.sqrt (1 - ρ ^ 2) * Real.sqrt (1 - ρ ^ 2) := by
          nlinarith [h_rho_D_le_sqrt, hsqrt_pos]
        _ = 1 - ρ ^ 2 := Real.mul_self_sqrt (by linarith)
    nlinarith [hν, h_mul_le]
  have h_comb : (ν - 2 * op) * D * (ρ * Real.sqrt (1 - ρ ^ 2)) ≤
      2 * L * (ρ * Real.sqrt (1 - ρ ^ 2)) := by
    calc
      (ν - 2 * op) * D * (ρ * Real.sqrt (1 - ρ ^ 2)) = (ν - 2 * op) * (ρ * D) * Real.sqrt (1 - ρ ^ 2) := by ring
      _ ≤ (ν - 2 * op) * (1 - ρ ^ 2) := h_chain
      _ ≤ 2 * ρ * Real.sqrt (1 - ρ ^ 2) * L := hmaster
      _ = 2 * L * (ρ * Real.sqrt (1 - ρ ^ 2)) := by ring
  have h_factor_pos : 0 < ρ * Real.sqrt (1 - ρ ^ 2) := mul_pos hρ_pos hsqrt_pos
  have h_D_bound : (ν - 2 * op) * D ≤ 2 * L := by
    exact le_of_mul_le_mul_right h_comb h_factor_pos
  rw [le_div_iff₀ hν]
  linarith [h_D_bound]

open WainwrightHDS.EigPert Matrix in
theorem solution {n : ℕ}
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (n + 2)) ℝ)
    (hUeig : ∀ j, ∃ μ : ℝ, S *ᵥ (fun i => U i j) = μ • (fun i => U i j))
    (hU0 : ∀ i, U i 0 = θstar i)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (hsmall : opNorm2 P < (gamma S hS.1 0 - gamma S hS.1 1) / 2) :
    (∃ θhat, IsMaxEigenvector (S + P) (hS.1.add hP) θhat) ∧
    (∀ v w, IsMaxEigenvector (S + P) (hS.1.add hP) v →
      IsMaxEigenvector (S + P) (hS.1.add hP) w → v = w ∨ v = -w) ∧
    (∀ θhat, IsMaxEigenvector (S + P) (hS.1.add hP) θhat → 0 ≤ inner ℝ θhat θstar →
      ‖θhat - θstar‖ ≤
        2 * ‖ptilde U P‖ / (gamma S hS.1 0 - gamma S hS.1 1 - 2 * opNorm2 P)) := by
  have _ := hUeig
  refine ⟨exists_maxEigenvector (S + P) (hS.1.add hP), ?_, ?_⟩
  · intro v w hv hw
    exact max_eigenvector_unique_up_to_sign S hS θstar hθstar hgap U hU hU0 P hP hsmall v w hv hw
  · intro θhat hθhat hρ
    have h_master := master_ineq S hS θstar hθstar hgap U hU hU0 P hP θhat hθhat hρ
    have hν : 0 < (gamma S hS.1 0 - gamma S hS.1 1) - 2 * opNorm2 P := by linarith
    have hρ1 : inner ℝ θhat θstar ≤ 1 := by
      have := real_inner_le_norm θhat θstar
      rw [hθhat.1, hθstar.1, mul_one] at this
      exact this
    have hD_sq : ‖θhat - θstar‖ ^ 2 = 2 * (1 - inner ℝ θhat θstar) := by
      rw [norm_sub_sq_real, hθhat.1, hθstar.1]
      ring
    exact pert_bound_of_master hν hρ hρ1 hD_sq (norm_nonneg _) (norm_nonneg _) h_master
