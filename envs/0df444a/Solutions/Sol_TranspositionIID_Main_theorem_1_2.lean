-- Prove2me | solution 1 for TranspositionIID.Main.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:10:18.630033+00:00
-- url     : https://prove2.me/submissions/9d34b4f1-9a4d-4565-8e12-322b8321aae6

import Mathlib
import Definitions.Def_TranspositionIID_Main_Stationary
import Theorems.Thm_TranspositionIID_Main_lemma_4_1
import Theorems.Thm_TranspositionIID_Main_lemma_4_2
import Theorems.Thm_TranspositionIID_Main_lemma_4_3

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Rev
open TranspositionIID.Main

variable {n : ℕ}

def pr (a : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  ⟨(a i).val - 1, by have := (a i).isLt; omega⟩

lemma T_pos {a : Equiv.Perm (Fin n)} {i : Fin n} (h : 0 < (a i).val) :
    transposeRequest a i = a.trans (Equiv.swap (a i) (pr a i)) := by
  unfold transposeRequest; rw [dif_pos h]; rfl

lemma T_zero {a : Equiv.Perm (Fin n)} {i : Fin n} (h : ¬ 0 < (a i).val) :
    transposeRequest a i = a := by
  unfold transposeRequest; rw [dif_neg h]

lemma kernel_nonneg (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) (a b : Equiv.Perm (Fin n)) :
    0 ≤ transpositionKernel q a b :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hq i]

lemma kernel_row (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) :
    ∑ b, transpositionKernel q a b = ∑ i, q i := by
  unfold transpositionKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma kernel_markov (q : Fin n → ℝ) (hq : ActuarialValuation.isFiniteStateDistribution q) :
    ActuarialValuation.isFiniteMarkovKernel (transpositionKernel q) :=
  ⟨kernel_nonneg q hq.1, fun a => by rw [kernel_row]; exact hq.2⟩

lemma pow_markov {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (t : ℕ) :
    (∀ a b, 0 ≤ (P ^ t) a b) ∧ ∀ a, ∑ b, (P ^ t) a b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> simp
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP.1 c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, (P ^ t) a c * P c b = ∑ c, (P ^ t) a c := by
            apply Finset.sum_congr rfl; intro c _
            rw [← Finset.mul_sum, hP.2 c, mul_one]
        _ = 1 := ih.2 a

lemma weight_swap (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) (i : Fin n) (h : 0 < (a i).val) :
    stationaryWeight q (a.trans (Equiv.swap (a i) (pr a i))) * q (a.symm (pr a i)) =
      stationaryWeight q a * q i := by
  set j := a.symm (pr a i) with hj
  have haj : a j = pr a i := by simp [hj]
  have hji : j ≠ i := by
    intro e; rw [e] at haj
    have := congrArg Fin.val haj
    simp [pr] at this; omega
  set z := a.trans (Equiv.swap (a i) (pr a i)) with hz
  have hzi : z i = pr a i := by simp [hz]
  have hzj : z j = a i := by simp [hz, haj]
  have hzk : ∀ k, k ≠ i → k ≠ j → z k = a k := by
    intro k hki hkj
    simp only [hz, Equiv.trans_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e; exact hki (a.injective e)
    · intro e; apply hkj; rw [← haj] at e; exact a.injective e
  have hprv : (pr a i).val = (a i).val - 1 := rfl
  have hlt := (a i).isLt
  unfold stationaryWeight
  have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hji]
  rw [← Finset.mul_prod_erase _ _ hmem_i, ← Finset.mul_prod_erase _ _ hmem_i,
    ← Finset.mul_prod_erase _ _ hmem_j, ← Finset.mul_prod_erase _ _ hmem_j]
  have hrest : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (z k).val) =
      ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (a k).val) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [hzk k hk.2.1 hk.1]
  rw [hrest, hzi, hzj, haj]
  have e1 : n - 1 - (pr a i).val = (n - 1 - (a i).val) + 1 := by rw [hprv]; omega
  have e2 : n - 1 - (a i).val + 1 = n - 1 - (pr a i).val := e1.symm
  rw [e1, pow_succ]
  ring

lemma detailed_balance_ne (q : Fin n → ℝ) (a z : Equiv.Perm (Fin n)) (hne : z ≠ a) :
    stationaryWeight q a * transpositionKernel q a z =
      stationaryWeight q z * transpositionKernel q z a := by
  unfold transpositionKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have key : ∀ i, transposeRequest a i = z → 0 < (a i).val := by
    intro i hi; by_contra h; rw [T_zero h] at hi; exact hne hi.symm
  have key2 : ∀ k, transposeRequest z k = a → 0 < (z k).val := by
    intro k hk; by_contra h; rw [T_zero h] at hk; exact hne hk
  have fwd : ∀ i, transposeRequest a i = z →
      transposeRequest z (a.symm (pr a i)) = a ∧ z (a.symm (pr a i)) = a i := by
    intro i hi
    have hp := key i hi
    rw [T_pos hp] at hi
    subst hi
    have hzk : (a.trans (Equiv.swap (a i) (pr a i))) (a.symm (pr a i)) = a i := by simp
    refine ⟨?_, hzk⟩
    rw [T_pos (by rw [hzk]; exact hp), hzk]
    have : pr (a.trans (Equiv.swap (a i) (pr a i))) (a.symm (pr a i)) = pr a i := by
      simp only [pr]; congr 1; simp
    rw [this]
    ext m; simp
  have bwd : ∀ k, transposeRequest z k = a →
      transposeRequest a (a.symm (z k)) = z ∧ a (a.symm (pr z k)) = pr z k ∧ a k = pr z k := by
    intro k hk
    have hp := key2 k hk
    rw [T_pos hp] at hk
    have hak : a k = pr z k := by
      rw [← hk]; simp
    have hz : z = a.trans (Equiv.swap (z k) (pr z k)) := by
      rw [← hk]; ext m; simp
    refine ⟨?_, by simp, hak⟩
    have h1 : a (a.symm (z k)) = z k := by simp
    have hp' : 0 < (a (a.symm (z k))).val := by rw [h1]; exact hp
    rw [T_pos hp']
    have : pr a (a.symm (z k)) = pr z k := by
      simp only [pr]; congr 1; rw [h1]
    rw [this, h1]
    exact hz.symm
  refine Finset.sum_bij' (fun i _ => a.symm (pr a i)) (fun k _ => a.symm (z k)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (fwd i hi).1
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact (bwd k hk).1
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [(fwd i hi).2]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := (bwd k hk).2.2
    have h2 : pr a (a.symm (z k)) = pr z k := by
      simp only [pr]; congr 1; simp
    show a.symm (pr a (a.symm (z k))) = k
    rw [h2, ← this]; simp
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hp := key i hi
    have := weight_swap q a i hp
    rw [← T_pos hp, hi] at this
    exact this.symm

lemma weight_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryWeight q a :=
  Finset.prod_pos fun i _ => pow_pos (hpos i) _

lemma partition_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) : 0 < partitionFunction q :=
  Finset.sum_pos (fun a _ => weight_pos q hpos a) Finset.univ_nonempty

lemma law_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryLaw q a :=
  div_pos (weight_pos q hpos a) (partition_pos q hpos)

lemma reversible_stationary (q : Fin n → ℝ)
    (hq : ActuarialValuation.isFiniteStateDistribution q) (hpos : ∀ i, 0 < q i) :
    ReversibleProbability (transpositionKernel q) (stationaryLaw q) := by
  have hZ := partition_pos q hpos
  have hdb : ∀ a z : Equiv.Perm (Fin n), stationaryLaw q a * transpositionKernel q a z =
      stationaryLaw q z * transpositionKernel q z a := by
    intro a z
    by_cases h : z = a
    · subst h; rfl
    · unfold stationaryLaw
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, detailed_balance_ne q a z h]
  refine ⟨⟨fun a => (law_pos q hpos a).le, ?_⟩, law_pos q hpos, ?_, hdb⟩
  · unfold stationaryLaw
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · intro z
    calc ∑ a, stationaryLaw q a * transpositionKernel q a z
        = ∑ a, stationaryLaw q z * transpositionKernel q z a :=
          Finset.sum_congr rfl fun a _ => hdb a z
      _ = stationaryLaw q z := by
          rw [← Finset.mul_sum, kernel_row, hq.2, mul_one]

end TranspositionIID.Main.Dev.Rev
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Chain
open TranspositionIID.Main

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma ennreal_half : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

lemma dir_eq (P : Matrix S S ℝ) (μ g : S → ℝ) (hc : ∀ a b, 0 ≤ μ a * P a b) (hg : ∀ a, 0 < g a) :
    entropyDissipation P μ g =
      ENNReal.ofReal (GibbsCongestion.dirichletForm P μ g (fun z => Real.log (g z))) := by
  have hterm : ∀ a b, 0 ≤ μ a * P a b * (g a - g b) * (Real.log (g a) - Real.log (g b)) := by
    intro a b
    have h1 : 0 ≤ (g a - g b) * (Real.log (g a) - Real.log (g b)) := by
      rcases le_total (g a) (g b) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (by linarith [Real.log_le_log (hg a) h])
      · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log (hg b) h])
    have := mul_nonneg (hc a b) h1
    linarith [this, show μ a * P a b * (g a - g b) * (Real.log (g a) - Real.log (g b)) =
      μ a * P a b * ((g a - g b) * (Real.log (g a) - Real.log (g b))) by ring]
  have hedge : ∀ a b, entropyEdge (μ a * P a b) (g a) (g b) =
      ENNReal.ofReal (μ a * P a b * (g a - g b) * (Real.log (g a) - Real.log (g b))) := by
    intro a b
    unfold entropyEdge
    by_cases h : μ a * P a b = 0
    · simp [h]
    · simp [h, (hg a).ne', (hg b).ne']
  unfold entropyDissipation GibbsCongestion.dirichletForm
  simp only [hedge]
  have hsum : ∑ a, ∑ b, ENNReal.ofReal (μ a * P a b * (g a - g b) * (Real.log (g a) - Real.log (g b))) =
      ENNReal.ofReal (∑ a, ∑ b, μ a * P a b * (g a - g b) * (Real.log (g a) - Real.log (g b))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => hterm a b)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_sum_of_nonneg (fun b _ => hterm a b)).symm
  rw [hsum, ennreal_half, ← ENNReal.ofReal_mul (by norm_num)]

lemma excess_nonneg {n : ℕ} (q : Fin n → ℝ) (z : ListState n) : 0 ≤ excess q z := by
  unfold excess optimum
  exact sub_nonneg.2 (csInf_le (Set.finite_range _).bddBelow ⟨z, rfl⟩)

lemma ceiling_nonneg {n : ℕ} (μ : ListState n → ℝ) (hμ : ActuarialValuation.isFiniteStateDistribution μ)
    (hpos : ∀ z, 0 < μ z) : 0 ≤ entropyCeiling μ := by
  unfold entropyCeiling
  obtain ⟨z0, hz0⟩ := (Set.range_nonempty μ).csInf_mem (Set.finite_range μ)
  rw [← hz0]
  have h1 : μ z0 ≤ 1 := by
    rw [← hμ.2]
    exact Finset.single_le_sum (f := μ) (fun i _ => hμ.1 i) (Finset.mem_univ z0)
  apply Real.log_nonneg
  rw [le_div_iff₀ (hpos z0)]; linarith

lemma chain_bound {n : ℕ} (hn : 1024 ≤ n) (q : Fin n → ℝ)
    (hq : ActuarialValuation.isFiniteStateDistribution q) (hsort : Decreasing q)
    (hpos : ∀ i, 0 < q i) (hH : entropyCeiling (stationaryLaw q) ≤ (n : ℝ) ^ 3 / 2)
    (σ : ListState n) (T : ℕ) (hT : n ^ 29 ≤ T) :
    expectedAfter (transpositionKernel q) σ T (excess q) ≤ 3 * C0 + 9 / 2 := by
  classical
  have hM := Rev.kernel_markov q hq
  have hrev := Rev.reversible_stationary q hq hpos
  have hμpos := Rev.law_pos q hpos
  obtain ⟨δ, hδ⟩ : ∃ δ : ListState n → ℝ, δ = fun a => if a = σ then 1 else 0 := ⟨_, rfl⟩
  have hlaw : ∀ t z, lawAfter (transpositionKernel q) δ t z = ((transpositionKernel q) ^ t) σ z := by
    intro t z; unfold lawAfter; simp [hδ]
  have hnn : ∀ t z, 0 ≤ lawAfter (transpositionKernel q) δ t z := fun t z => by
    rw [hlaw]; exact (Rev.pow_markov _ hM t).1 σ z
  have hsum : ∀ t, ∑ z, lawAfter (transpositionKernel q) δ t z = 1 := fun t => by
    simp_rw [hlaw]; exact (Rev.pow_markov _ hM t).2 σ
  have hδd : ActuarialValuation.isFiniteStateDistribution δ := by
    refine ⟨fun a => ?_, ?_⟩
    · rw [hδ]; dsimp only; split_ifs <;> norm_num
    · rw [hδ]; simp
  obtain ⟨g, hg⟩ : ∃ g : ListState n → ℝ,
      g = smoothedDensity (transpositionKernel q) (stationaryLaw q) δ T := ⟨_, rfl⟩
  have hf : ∀ t z, 0 ≤ densityAfter (transpositionKernel q) (stationaryLaw q) δ t z :=
    fun t z => div_nonneg (hnn t z) (hμpos z).le
  have hgz : ∀ z, g z = (1 + densityAfter (transpositionKernel q) (stationaryLaw q) δ T z +
      densityAfter (transpositionKernel q) (stationaryLaw q) δ (T + 1) z) / 3 := by
    intro z; rw [hg]; rfl
  have hgpos : ∀ z, 0 < g z := fun z => by
    rw [hgz]; linarith [hf T z, hf (T + 1) z]
  have hμf : ∀ t z, stationaryLaw q z * densityAfter (transpositionKernel q) (stationaryLaw q) δ t z =
      lawAfter (transpositionKernel q) δ t z := by
    intro t z; unfold densityAfter; field_simp [(hμpos z).ne']
  obtain ⟨ν', hν'⟩ : ∃ ν' : ListState n → ℝ, ∀ z, ν' z = stationaryLaw q z * g z := ⟨_, fun _ => rfl⟩
  have hν'eq : ∀ z, ν' z = (stationaryLaw q z + lawAfter (transpositionKernel q) δ T z +
      lawAfter (transpositionKernel q) δ (T + 1) z) / 3 := by
    intro z
    rw [hν', hgz, ← hμf T z, ← hμf (T + 1) z]; ring
  have hν'd : ActuarialValuation.isFiniteStateDistribution ν' := by
    refine ⟨fun z => ?_, ?_⟩
    · rw [hν']; exact mul_nonneg (hμpos z).le (hgpos z).le
    · simp_rw [hν'eq, ← Finset.sum_div, Finset.sum_add_distrib, hsum, hrev.1.2]; norm_num
  have h41 := lemma_4_1 hn q hq hsort hpos ν' hν'd
  have hfun : (fun σ => ν' σ / stationaryLaw q σ) = g := by
    funext z; rw [hν']; field_simp [(hμpos z).ne']
  have hc : ∀ a b, 0 ≤ stationaryLaw q a * transpositionKernel q a b := fun a b =>
    mul_nonneg (hμpos a).le (Rev.kernel_nonneg q hq.1 a b)
  have hE := dir_eq (transpositionKernel q) (stationaryLaw q) g hc hgpos
  rw [hfun, hE] at h41
  have h42 := lemma_4_2 (transpositionKernel q) hM (stationaryLaw q) hrev δ hδd T
  rw [← hg] at h42
  -- numerics
  have hm : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < n := by linarith
  have hH0 := ceiling_nonneg (stationaryLaw q) hrev.1 hμpos
  have hTr : (n : ℝ) ^ 29 ≤ T := by exact_mod_cast hT
  set m : ℝ := (n : ℝ) with hmdef
  set H := entropyCeiling (stationaryLaw q) with hHdef
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hm3 : (1 : ℝ) ≤ m ^ 3 := one_le_pow₀ (by linarith)
  have hsq : Real.sqrt (H / (2 * ((T : ℝ) + 1))) ≤ (m ^ 13)⁻¹ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have hT1 : m ^ 29 ≤ (T : ℝ) + 1 := by linarith
    have h1 : ((m ^ 13)⁻¹) ^ 2 * m ^ 29 = m ^ 3 := by field_simp
    have h2 : ((m ^ 13)⁻¹) ^ 2 * (2 * m ^ 29) ≤ ((m ^ 13)⁻¹) ^ 2 * (2 * ((T : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [h1, h2, hH, hm3]
  have hB : ((H + Real.log 3) / 3) * Real.sqrt (H / (2 * ((T : ℝ) + 1))) ≤ (((m ^ 5)⁻¹) ^ 2) := by
    have h1 : (H + Real.log 3) / 3 ≤ m ^ 3 := by nlinarith [hH, hm3]
    calc ((H + Real.log 3) / 3) * Real.sqrt (H / (2 * ((T : ℝ) + 1)))
        ≤ m ^ 3 * (m ^ 13)⁻¹ :=
          mul_le_mul h1 hsq (Real.sqrt_nonneg _) (by positivity)
      _ = ((m ^ 5)⁻¹) ^ 2 := by field_simp
  have hs0 : 0 ≤ (m ^ 5)⁻¹ := by positivity
  have hE' : ENNReal.ofReal (GibbsCongestion.dirichletForm (transpositionKernel q) (stationaryLaw q) g
      (fun z => Real.log (g z))) ≤ ENNReal.ofReal (((m ^ 5)⁻¹) ^ 2) :=
    ENNReal.ofReal_le_ofReal (h42.trans hB)
  have hE2 := ENNReal.rpow_le_rpow hE' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hs0] at hE2
  have h43 : ENNReal.ofReal (∑ z, ν' z * excess q z) ≤ ENNReal.ofReal (C0 + 3 / 2) := by
    calc ENNReal.ofReal (∑ z, ν' z * excess q z)
        ≤ ENNReal.ofReal C0 + ENNReal.ofReal ((3 / 2 : ℝ) * m ^ 5) *
            ENNReal.ofReal ((m ^ 5)⁻¹) := by
          refine h41.trans ?_
          exact add_le_add le_rfl (mul_le_mul' le_rfl hE2)
      _ = ENNReal.ofReal (C0 + 3 / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by unfold C0; positivity)
            (by positivity)]
          congr 1
          field_simp
  have hC0 : 0 ≤ C0 := by unfold C0; positivity
  have h44 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h43
  calc expectedAfter (transpositionKernel q) σ T (excess q)
      = ∑ z, ((transpositionKernel q) ^ T) σ z * excess q z := rfl
    _ ≤ ∑ z, 3 * (ν' z * excess q z) := by
        apply Finset.sum_le_sum
        intro z _
        have h1 : lawAfter (transpositionKernel q) δ T z ≤ 3 * ν' z := by
          rw [hν'eq]; linarith [hnn (T + 1) z, (hμpos z).le]
        rw [← hlaw]
        calc lawAfter (transpositionKernel q) δ T z * excess q z
            ≤ (3 * ν' z) * excess q z := mul_le_mul_of_nonneg_right h1 (excess_nonneg q z)
          _ = 3 * (ν' z * excess q z) := by ring
    _ = 3 * ∑ z, ν' z * excess q z := by rw [← Finset.mul_sum]
    _ ≤ 3 * (C0 + 3 / 2) := by linarith
    _ = 3 * C0 + 9 / 2 := by ring

end TranspositionIID.Main.Dev.Chain
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Thm12
open TranspositionIID.Main
open TranspositionIID.Main.Dev

lemma exp_cost {n : ℕ} (p : Fin n → ℝ) (hp : ActuarialValuation.isFiniteStateDistribution p)
    (σ : ListState n) (t : ℕ) :
    expectedAfter (transpositionKernel p) σ t (cost p) =
      expectedAfter (transpositionKernel p) σ t (excess p) + optimum p := by
  have hM := Rev.kernel_markov p hp
  have h1 := (Rev.pow_markov _ hM t).2 σ
  unfold expectedAfter
  have : ∑ z, ((transpositionKernel p) ^ t) σ z * cost p z =
      ∑ z, ((transpositionKernel p) ^ t) σ z * excess p z +
        optimum p * ∑ z, ((transpositionKernel p) ^ t) σ z := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    unfold excess; ring
  rw [this, h1]; ring

lemma small_case {n : ℕ} (hn : n < 1024) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p) (σ : ListState n) (t : ℕ) :
    expectedAfter (transpositionKernel p) σ t (excess p) ≤ 1250 := by
  have hM := Rev.kernel_markov p hp
  have hcost_le : ∀ z, cost p z ≤ n := by
    intro z
    calc cost p z = ∑ i, p i * (((z i).val + 1 : ℕ) : ℝ) := rfl
      _ ≤ ∑ i, p i * (n : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (hp.1 i)
          exact_mod_cast (z i).isLt
      _ = n := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hopt : 1 ≤ optimum p := by
    unfold optimum
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    calc (1 : ℝ) = ∑ i, p i * 1 := by simp [hp.2]
      _ ≤ cost p z := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (hp.1 i)
          norm_cast; omega
  have hex : ∀ z, excess p z ≤ 1250 := by
    intro z
    have : (n : ℝ) < 1024 := by exact_mod_cast hn
    unfold excess; linarith [hcost_le z]
  calc expectedAfter (transpositionKernel p) σ t (excess p)
      = ∑ z, ((transpositionKernel p) ^ t) σ z * excess p z := rfl
    _ ≤ ∑ z, ((transpositionKernel p) ^ t) σ z * 1250 := by
        apply Finset.sum_le_sum; intro z _
        exact mul_le_mul_of_nonneg_left (hex z) ((Rev.pow_markov _ hM t).1 σ z)
    _ = 1250 := by rw [← Finset.sum_mul, (Rev.pow_markov _ hM t).2 σ, one_mul]

lemma C0_le : C0 ≤ 405 := by
  unfold C0
  have he : Real.exp 1 ≤ 2.72 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hs : Real.sqrt (Real.exp 1) ≤ 1.66 := by
    rw [Real.sqrt_le_iff]; constructor <;> nlinarith
  have hs0 : 0 ≤ Real.sqrt (Real.exp 1) := Real.sqrt_nonneg _
  have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hy : Real.pi ^ 2 ≤ 9.93 := by nlinarith
  have h1 : (2 * Real.pi ^ 2 / 3) * (1 + 8 * Real.exp 1) ≤ (2 * 9.93 / 3) * (1 + 8 * 2.72) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have h2 : (1 + Real.sqrt (Real.exp 1)) * (1 / 4 + (2 * Real.pi ^ 2 / 3) * (1 + 8 * Real.exp 1)) ≤
      (1 + 1.66) * (1 / 4 + (2 * 9.93 / 3) * (1 + 8 * 2.72)) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have : (2 : ℝ) + (1 + 1.66) * (1 / 4 + (2 * 9.93 / 3) * (1 + 8 * 2.72)) ≤ 405 := by norm_num
  linarith

lemma tail_small {n : ℕ} (hn : 1024 ≤ n) :
    ((n ^ 29 : ℕ) + 1 : ℝ) * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) ≤ 1 := by
  have hm : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) with hmdef
  have hm1 : (1 : ℝ) ≤ m ^ 29 := one_le_pow₀ (by linarith)
  have hexp : (m / 124) ^ 124 ≤ Real.exp m := by
    have h1 : m / 124 ≤ Real.exp (m / 124) := by linarith [Real.add_one_le_exp (m / 124)]
    calc (m / 124) ^ 124 ≤ (Real.exp (m / 124)) ^ 124 :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = Real.exp m := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hbig : 2 * m ^ 31 ≤ (m / 124) ^ 124 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h1 : (1024 : ℝ) ^ 93 ≤ m ^ 93 := pow_le_pow_left₀ (by norm_num) hm _
    have h2 : (2 : ℝ) * 124 ^ 124 ≤ 1024 ^ 93 := by norm_num
    have h3 : m ^ 124 = m ^ 31 * m ^ 93 := by ring
    rw [h3]
    nlinarith [pow_pos (show (0:ℝ) < m by linarith) 31]
  push_cast
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  have : (m ^ 29 + 1) * m ^ 2 ≤ 2 * m ^ 31 := by
    have : m ^ 31 = m ^ 29 * m ^ 2 := by ring
    nlinarith [pow_pos (show (0:ℝ) < m by linarith) 2]
  linarith

lemma big_sorted {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p) (hsort : Decreasing p)
    (σ₀ : ListState n) (t : ℕ) (ht : n ^ 29 ≤ t) :
    expectedAfter (transpositionKernel p) σ₀ t (excess p) ≤ 1250 := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hqd, hqpos, hqord, hcoup, hH⟩ := lemma_4_3 hn2 p hp hsort
  have hqsort : Decreasing (perturb p) := fun i j hij => (hqord j i).2 (hsort hij)
  have hM := Rev.kernel_markov p hp
  have hC0 := C0_le
  have htail := tail_small hn
  have hbound : ∀ η : ListState n,
      expectedAfter (transpositionKernel p) η (n ^ 29) (excess p) ≤ 1250 := by
    intro η
    have h1 := hcoup η (n ^ 29)
    have h2 := Chain.chain_bound hn (perturb p) hqd hqsort hqpos hH η (n ^ 29) le_rfl
    push_cast at h1 htail
    linarith
  obtain ⟨s, rfl⟩ : ∃ s, t = s + n ^ 29 := ⟨t - n ^ 29, by omega⟩
  calc expectedAfter (transpositionKernel p) σ₀ (s + n ^ 29) (excess p)
      = ∑ z, ∑ η, ((transpositionKernel p) ^ s) σ₀ η *
          (((transpositionKernel p) ^ (n ^ 29)) η z * excess p z) := by
        unfold expectedAfter
        apply Finset.sum_congr rfl; intro z _
        rw [pow_add, Matrix.mul_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro η _; ring
    _ = ∑ η, ((transpositionKernel p) ^ s) σ₀ η *
          expectedAfter (transpositionKernel p) η (n ^ 29) (excess p) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro η _
        unfold expectedAfter
        rw [Finset.mul_sum]
    _ ≤ ∑ η, ((transpositionKernel p) ^ s) σ₀ η * 1250 := by
        apply Finset.sum_le_sum; intro η _
        exact mul_le_mul_of_nonneg_left (hbound η) ((Rev.pow_markov _ hM s).1 σ₀ η)
    _ = 1250 := by rw [← Finset.sum_mul, (Rev.pow_markov _ hM s).2 σ₀, one_mul]

end TranspositionIID.Main.Dev.Thm12
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Relabel
open TranspositionIID.Main
open TranspositionIID.Main.Dev

variable {n : ℕ}

lemma T_mul (σ τ : Equiv.Perm (Fin n)) (k : Fin n) :
    transposeRequest (σ * τ) k = transposeRequest σ (τ k) * τ := by
  unfold transposeRequest
  by_cases h : 0 < (σ (τ k)).val
  · have h' : 0 < ((σ * τ) k).val := h
    rw [dif_pos h', dif_pos h]
    ext m; simp [Equiv.Perm.mul_apply]
  · have h' : ¬ 0 < ((σ * τ) k).val := h
    rw [dif_neg h', dif_neg h]

lemma kernel_relabel (p : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (σ η : Equiv.Perm (Fin n)) :
    transpositionKernel p σ η =
      transpositionKernel (fun k => p (τ k)) (σ * τ) (η * τ) := by
  unfold transpositionKernel
  rw [← Equiv.sum_comp τ]
  apply Finset.sum_congr rfl; intro k _
  simp only [T_mul, mul_left_inj]

lemma pow_relabel (p : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (t : ℕ) (σ η : Equiv.Perm (Fin n)) :
    ((transpositionKernel p) ^ t) σ η =
      ((transpositionKernel (fun k => p (τ k))) ^ t) (σ * τ) (η * τ) := by
  induction t generalizing η with
  | zero => simp [Matrix.one_apply, mul_left_inj]
  | succ t ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulRight τ) (fun c =>
      ((transpositionKernel (fun k => p (τ k))) ^ t) (σ * τ) c *
        transpositionKernel (fun k => p (τ k)) c (η * τ)))
    apply Finset.sum_congr rfl; intro c _
    show _ = ((transpositionKernel (fun k => p (τ k))) ^ t) (σ * τ) (c * τ) *
        transpositionKernel (fun k => p (τ k)) (c * τ) (η * τ)
    rw [ih c, kernel_relabel p τ c η]

lemma cost_relabel (p : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) :
    cost p σ = cost (fun k => p (τ k)) (σ * τ) := by
  unfold cost
  rw [← Equiv.sum_comp τ]
  rfl

lemma opt_relabel (p : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) :
    optimum p = optimum (fun k => p (τ k)) := by
  unfold optimum
  congr 1
  ext r
  constructor
  · rintro ⟨σ, rfl⟩; exact ⟨σ * τ, (cost_relabel p τ σ).symm⟩
  · rintro ⟨σ', rfl⟩
    refine ⟨σ' * τ⁻¹, ?_⟩
    rw [cost_relabel p τ, mul_assoc, inv_mul_cancel, mul_one]

lemma exp_relabel (p : Fin n → ℝ) (τ : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) :
    expectedAfter (transpositionKernel p) σ t (cost p) =
      expectedAfter (transpositionKernel (fun k => p (τ k))) (σ * τ) t
        (cost (fun k => p (τ k))) := by
  unfold expectedAfter
  refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulRight τ) (fun z =>
    ((transpositionKernel (fun k => p (τ k))) ^ t) (σ * τ) z * cost (fun k => p (τ k)) z))
  apply Finset.sum_congr rfl; intro z _
  show _ = ((transpositionKernel (fun k => p (τ k))) ^ t) (σ * τ) (z * τ) *
    cost (fun k => p (τ k)) (z * τ)
  rw [pow_relabel p τ t σ z, cost_relabel p τ z]

end TranspositionIID.Main.Dev.Relabel

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev

theorem chk_theorem_1_2 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (σ₀ : ListState n) (t : ℕ) (ht : n ^ 29 ≤ t) :
    expectedAfter (transpositionKernel p) σ₀ t (cost p) ≤ optimum p + 1250 := by
  by_cases hsmall : n < 1024
  · rw [Thm12.exp_cost p hp]
    linarith [Thm12.small_case hsmall p hp σ₀ t]
  · have hbig : 1024 ≤ n := by omega
    obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), Antitone (fun k => p (τ k)) := by
      refine ⟨Tuple.sort (fun i => -p i), ?_⟩
      intro i j hij
      have := Tuple.monotone_sort (fun i => -p i) hij
      simp only [Function.comp] at this
      linarith
    have hp' : ActuarialValuation.isFiniteStateDistribution (fun k => p (τ k)) :=
      ⟨fun k => hp.1 _, by rw [Equiv.sum_comp τ p]; exact hp.2⟩
    rw [Relabel.exp_relabel p τ σ₀ t, Thm12.exp_cost _ hp', ← Relabel.opt_relabel p τ]
    linarith [Thm12.big_sorted hbig (fun k => p (τ k)) hp' hτ (σ₀ * τ) t ht]

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_theorem_1_2 := @TranspositionIID.Main.chk_theorem_1_2
