-- Prove2me | solution 1 for SubsampVB.Consist.lemma_1_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:03:43.496203+00:00
-- url     : https://prove2.me/submissions/cd2abbbf-d11b-403f-b840-e19e7138631c

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting

open MeasureTheory Filter Finset ProbabilityTheory SubsampVB.Consist

universe u

namespace SVBLemma1Aux

/-- `∑ (zₖ - z̄)² = ∑ zₖ² - K z̄²`. -/
lemma sum_sq_dev {K : ℕ} (hK : K ≠ 0) (z : Fin K → ℝ) :
    ∑ k, (z k - (K : ℝ)⁻¹ * ∑ j, z j) ^ 2 =
      ∑ k, z k ^ 2 - K * ((K : ℝ)⁻¹ * ∑ j, z j) ^ 2 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  field_simp
  ring

/-- Expected sum of squared deviations of independent square-integrable variables. -/
lemma expected_ssd {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℕ} (hK : K ≠ 0) (Z : Fin K → Ω → ℝ) (hZ : ∀ k, MemLp (Z k) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (Z i) (Z j) μ) :
    ∫ ω, ∑ k, (Z k ω - (K : ℝ)⁻¹ * ∑ j, Z j ω) ^ 2 ∂μ =
      ∑ k, (μ[Z k] - (K : ℝ)⁻¹ * ∑ j, μ[Z j]) ^ 2 +
        (1 - (K : ℝ)⁻¹) * ∑ k, Var[Z k; μ] := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have hsum : MemLp (fun ω => ∑ j, Z j ω) 2 μ := memLp_finsetSum univ (fun j _ => hZ j)
  have hbar : MemLp (fun ω => (K : ℝ)⁻¹ * ∑ j, Z j ω) 2 μ := hsum.const_mul _
  simp_rw [sum_sq_dev hK]
  rw [integral_sub (integrable_finsetSum _ (fun k _ => (hZ k).integrable_sq))
    (hbar.integrable_sq.const_mul _), integral_finsetSum _ (fun k _ => (hZ k).integrable_sq),
    integral_const_mul]
  have hsq : ∀ k, ∫ ω, Z k ω ^ 2 ∂μ = Var[Z k; μ] + μ[Z k] ^ 2 := by
    intro k
    rw [variance_eq_sub (hZ k)]
    simp [Pi.pow_apply]
  have hvar_sum : Var[fun ω => ∑ j, Z j ω; μ] = ∑ j, Var[Z j; μ] := by
    have := IndepFun.variance_sum (s := univ) (fun j _ => hZ j)
      (fun i _ j _ hij => hind i j hij)
    rw [← this]
    congr 1
    ext ω
    simp [Finset.sum_apply]
  have hbarsq : ∫ ω, ((K : ℝ)⁻¹ * ∑ j, Z j ω) ^ 2 ∂μ =
      ((K : ℝ)⁻¹) ^ 2 * ∑ j, Var[Z j; μ] + ((K : ℝ)⁻¹ * ∑ j, μ[Z j]) ^ 2 := by
    have h1 := variance_eq_sub hbar
    have h2 : Var[fun ω => (K : ℝ)⁻¹ * ∑ j, Z j ω; μ] = ((K : ℝ)⁻¹) ^ 2 * ∑ j, Var[Z j; μ] := by
      rw [variance_const_mul, hvar_sum]
    have h3 : μ[fun ω => (K : ℝ)⁻¹ * ∑ j, Z j ω] = (K : ℝ)⁻¹ * ∑ j, μ[Z j] := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hZ j).integrable one_le_two)]
    have h4 : ∫ ω, ((K : ℝ)⁻¹ * ∑ j, Z j ω) ^ 2 ∂μ =
        μ[(fun ω => (K : ℝ)⁻¹ * ∑ j, Z j ω) ^ 2] := by simp [Pi.pow_apply]
    rw [h4]
    rw [h2, h3] at h1
    linarith
  simp_rw [hsq]
  rw [hbarsq, Finset.sum_add_distrib]
  field_simp
  ring

/-- Second moment `∑ⱼ` over a uniform product: finite-sum version of the unbiasedness of the
sample variance of i.i.d. uniform draws. -/
lemma sum_pi_single {J : Type*} [Fintype J] {B : ℕ} (b : Fin B) (φ : J → ℝ) :
    ∑ I : Fin B → J, φ (I b) = (Fintype.card J : ℝ) ^ (B - 1) * ∑ j, φ j := by
  classical
  have := Finset.prod_univ_sum (fun _ : Fin B => (univ : Finset J))
    (fun c j => if c = b then φ j else 1)
  simp only [Fintype.piFinset_univ] at this
  have h2 : ∀ I : Fin B → J, ∏ c, (if c = b then φ (I c) else 1) = φ (I b) := by
    intro I
    rw [Finset.prod_ite_eq' univ b (fun c => φ (I c))]
    simp
  simp_rw [h2] at this
  rw [← this, ← Finset.mul_prod_erase univ _ (Finset.mem_univ b)]
  have h3 : ∀ i ∈ univ.erase b, (∑ j : J, if i = b then φ j else 1) =
      (Fintype.card J : ℝ) := by
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  rw [Finset.prod_congr rfl h3, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ, Fintype.card_fin]
  simp only [if_true]
  ring

lemma sum_pi_pair {J : Type*} [Fintype J] {B : ℕ} {b b' : Fin B} (hbb : b ≠ b')
    (φ ϕ : J → ℝ) (hφ : ∑ j, φ j = 0) :
    ∑ I : Fin B → J, φ (I b) * ϕ (I b') = 0 := by
  classical
  have := Finset.prod_univ_sum (fun _ : Fin B => (univ : Finset J))
    (fun c j => (if c = b then φ j else 1) * (if c = b' then ϕ j else 1))
  simp only [Fintype.piFinset_univ] at this
  have h2 : ∀ I : Fin B → J, ∏ c, ((if c = b then φ (I c) else 1) *
      (if c = b' then ϕ (I c) else 1)) = φ (I b) * ϕ (I b') := by
    intro I
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ b (fun c => φ (I c)),
      Finset.prod_ite_eq' univ b' (fun c => ϕ (I c))]
    simp
  simp_rw [h2] at this
  rw [← this]
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  simp [hbb, hφ]

lemma stepB {J : Type*} [Fintype J] [Nonempty J] {B : ℕ} (hB : 2 ≤ B) (f : J → ℝ) :
    (Fintype.card (Fin B → J) : ℝ)⁻¹ * ∑ I : Fin B → J,
        ((B - 1 : ℝ)⁻¹ * ∑ b, (f (I b) - (B : ℝ)⁻¹ * ∑ b', f (I b')) ^ 2) =
      (Fintype.card J : ℝ)⁻¹ * ∑ j, (f j - (Fintype.card J : ℝ)⁻¹ * ∑ j', f j') ^ 2 := by
  classical
  set N : ℕ := Fintype.card J with hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB0 : (B : ℕ) ≠ 0 := by omega
  have hB0' : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
  have hB1 : (B : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  set mean := (N : ℝ)⁻¹ * ∑ j', f j' with hmean
  set gg : J → ℝ := fun j => f j - mean with hgg
  have hgsum : ∑ j, gg j = 0 := by
    simp only [hgg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hN, hmean]
    field_simp
    ring
  -- rewrite deviations in terms of the centred function
  have hdev : ∀ I : Fin B → J, ∑ b, (f (I b) - (B : ℝ)⁻¹ * ∑ b', f (I b')) ^ 2 =
      ∑ b, gg (I b) ^ 2 - (B : ℝ)⁻¹ * ∑ b, ∑ b', gg (I b) * gg (I b') := by
    intro I
    have e : ∀ b, f (I b) - (B : ℝ)⁻¹ * ∑ b', f (I b') =
        gg (I b) - (B : ℝ)⁻¹ * ∑ b', gg (I b') := by
      intro b
      simp only [hgg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    simp_rw [e]
    rw [sum_sq_dev hB0 (fun b => gg (I b))]
    rw [← Finset.sum_mul_sum]
    field_simp
  simp_rw [hdev]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hdiag : ∀ b : Fin B, ∑ I : Fin B → J, gg (I b) ^ 2 =
      (N : ℝ) ^ (B - 1) * ∑ j, gg j ^ 2 := fun b => sum_pi_single b (fun j => gg j ^ 2)
  have hcross : ∀ I : Fin B → J, ∑ b, ∑ b', gg (I b) * gg (I b') =
      ∑ b, ∑ b', gg (I b) * gg (I b') := fun I => rfl
  have hcross2 : ∑ I : Fin B → J, ∑ b, ∑ b', gg (I b) * gg (I b') =
      ∑ b : Fin B, (N : ℝ) ^ (B - 1) * ∑ j, gg j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single b]
    · rw [← hdiag b]; simp [sq]
    · intro b' _ hb'
      exact sum_pi_pair (Ne.symm hb') gg gg hgsum
    · simp
  have hD : ∑ I : Fin B → J, ∑ b, gg (I b) ^ 2 = B * ((N : ℝ) ^ (B - 1) * ∑ j, gg j ^ 2) := by
    rw [Finset.sum_comm]
    simp_rw [hdiag]
    simp
  have hC : ∑ I : Fin B → J, (B : ℝ)⁻¹ * ∑ b, ∑ b', gg (I b) * gg (I b') =
      (B : ℝ)⁻¹ * (B * ((N : ℝ) ^ (B - 1) * ∑ j, gg j ^ 2)) := by
    rw [← Finset.mul_sum, hcross2]
    simp
  rw [hD, hC]
  have hR : ∑ j, (f j - mean) ^ 2 = ∑ j, gg j ^ 2 := rfl
  rw [hR]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← hN]
  have hpow : (N : ℝ) ^ B = (N : ℝ) ^ (B - 1) * N := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  have hNp : (N : ℝ) ^ (B - 1) ≠ 0 := pow_ne_zero _ hN0
  field_simp

/-- Transport an integral along a measure-preserving map. -/
lemma integral_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {e : α → β} (he : MeasurePreserving e μ ν) {g : β → ℝ}
    (hg : AEStronglyMeasurable g ν) : ∫ x, g (e x) ∂μ = ∫ y, g y ∂ν := by
  rw [← he.map_eq] at hg ⊢
  rw [integral_map he.measurable.aemeasurable hg]

/-- Exact expectation of Algorithm 2's output for fixed resamples. -/
lemma stepA {B R : ℕ} (hB : 2 ≤ B) (hR : 2 ≤ R) (ν : Fin B → Measure ℝ)
    [∀ b, IsProbabilityMeasure (ν b)] (hν : ∀ b, MemLp (fun y : ℝ => y) 2 (ν b)) (θ : ℝ) :
    ∫ Y, sigmaHatSVB θ Y ∂(Measure.pi (fun b => Measure.pi (fun _ : Fin R => ν b))) =
      θ * ((B - 1 : ℝ)⁻¹ * ∑ b, ((∫ y, y ∂(ν b)) -
        (B : ℝ)⁻¹ * ∑ b', ∫ y, y ∂(ν b')) ^ 2) := by
  set μ := Measure.pi (fun b => Measure.pi (fun _ : Fin R => ν b)) with hμ
  have hB0 : (B : ℕ) ≠ 0 := by omega
  have hR0 : (R : ℕ) ≠ 0 := by omega
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hRr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  set a : Fin B → ℝ := fun b => ∫ y, y ∂(ν b) with ha
  set v : Fin B → ℝ := fun b => Var[fun y : ℝ => y; ν b] with hv
  -- inner product measures
  have hin_eval : ∀ b (r : Fin R), MeasurePreserving (fun z : Fin R → ℝ => z r)
      (Measure.pi (fun _ : Fin R => ν b)) (ν b) := fun b r => measurePreserving_eval _ r
  have hout_eval : ∀ b, MeasurePreserving (fun Y : Fin B → Fin R → ℝ => Y b) μ
      (Measure.pi (fun _ : Fin R => ν b)) := fun b => measurePreserving_eval _ b
  have hin_L2 : ∀ b (r : Fin R), MemLp (fun z : Fin R → ℝ => z r) 2
      (Measure.pi (fun _ : Fin R => ν b)) := fun b r =>
    (hν b).comp_measurePreserving (hin_eval b r)
  have hin_ind : ∀ b (r r' : Fin R), r ≠ r' → IndepFun (fun z : Fin R → ℝ => z r)
      (fun z : Fin R → ℝ => z r') (Measure.pi (fun _ : Fin R => ν b)) := by
    intro b r r' hrr
    have := iIndepFun_pi (μ := fun _ : Fin R => ν b) (X := fun _ (y : ℝ) => y)
      (fun _ => measurable_id.aemeasurable)
    exact this.indepFun hrr
  -- the inner mean as a function on `Fin R → ℝ`
  set gm : (Fin R → ℝ) → ℝ := fun z => (R : ℝ)⁻¹ * ∑ r, z r with hgm
  have hgm_meas : Measurable gm := by
    simp only [hgm]; fun_prop
  have hgm_L2 : ∀ b, MemLp gm 2 (Measure.pi (fun _ : Fin R => ν b)) := fun b =>
    (memLp_finsetSum univ (fun r _ => hin_L2 b r)).const_mul _
  have hgm_int : ∀ b, ∫ z, gm z ∂(Measure.pi (fun _ : Fin R => ν b)) = a b := by
    intro b
    simp only [hgm]
    rw [integral_const_mul, integral_finsetSum _ (fun r _ => (hin_L2 b r).integrable one_le_two)]
    simp_rw [fun r => integral_mp (hin_eval b r) (g := fun y : ℝ => y)
      aestronglyMeasurable_id]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (R : ℝ) ≠ 0 := by exact_mod_cast hR0
    field_simp
    rfl
  have hgm_var : ∀ b, Var[gm; Measure.pi (fun _ : Fin R => ν b)] = v b / R := by
    intro b
    simp only [hgm]
    rw [variance_const_mul]
    have := IndepFun.variance_sum (s := univ) (fun r _ => hin_L2 b r)
      (fun r _ r' _ hrr => hin_ind b r r' hrr)
    have e : (fun z : Fin R → ℝ => ∑ r, z r) = ∑ r : Fin R, (fun z : Fin R → ℝ => z r) := by
      ext z; simp [Finset.sum_apply]
    rw [e, this]
    simp_rw [fun r => (hin_eval b r).variance_fun_comp (f := fun y : ℝ => y)
      measurable_id.aemeasurable]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hv]
    have : (R : ℝ) ≠ 0 := by exact_mod_cast hR0
    field_simp
  -- group means on the outer product
  set G : Fin B → (Fin B → Fin R → ℝ) → ℝ := fun b Y => gm (Y b) with hG
  have hG_L2 : ∀ b, MemLp (G b) 2 μ := fun b => (hgm_L2 b).comp_measurePreserving (hout_eval b)
  have hG_ind : ∀ b b', b ≠ b' → IndepFun (G b) (G b') μ := by
    intro b b' hbb
    have := iIndepFun_pi (μ := fun b => Measure.pi (fun _ : Fin R => ν b))
      (X := fun _ (z : Fin R → ℝ) => z) (fun _ => measurable_id.aemeasurable)
    exact (this.indepFun hbb).comp hgm_meas hgm_meas
  have hG_int : ∀ b, μ[G b] = a b := fun b => by
    rw [← hgm_int b]
    exact integral_mp (hout_eval b) hgm_meas.aestronglyMeasurable
  have hG_var : ∀ b, Var[G b; μ] = v b / R := fun b => by
    rw [← hgm_var b]
    exact (hout_eval b).variance_fun_comp hgm_meas.aemeasurable
  -- between-group term
  have hbetween : ∫ Y, ∑ b, (groupMean Y b - grandMean Y) ^ 2 ∂μ =
      ∑ b, (a b - (B : ℝ)⁻¹ * ∑ b', a b') ^ 2 + (1 - (B : ℝ)⁻¹) * ∑ b, v b / R := by
    have := expected_ssd hB0 G hG_L2 hG_ind
    simp_rw [hG_int, hG_var] at this
    rw [← this]
    rfl
  -- within-group term
  have hwithin_b : ∀ b, ∫ Y, ∑ r, (Y b r - groupMean Y b) ^ 2 ∂μ = (R - 1 : ℝ) * v b := by
    intro b
    have hmeas : Measurable (fun z : Fin R → ℝ => ∑ r, (z r - gm z) ^ 2) := by
      simp only [hgm]; fun_prop
    have := integral_mp (hout_eval b) hmeas.aestronglyMeasurable
    rw [show (fun Y : Fin B → Fin R → ℝ => ∑ r, (Y b r - groupMean Y b) ^ 2) =
      fun Y => (fun z : Fin R → ℝ => ∑ r, (z r - gm z) ^ 2) (Y b) from rfl, this]
    have h2 := expected_ssd hR0 (fun r (z : Fin R → ℝ) => z r) (hin_L2 b)
      (hin_ind b)
    simp only [hgm]
    rw [h2]
    simp_rw [fun r => integral_mp (hin_eval b r) (g := fun y : ℝ => y)
      aestronglyMeasurable_id]
    simp_rw [fun r => (hin_eval b r).variance_fun_comp (f := fun y : ℝ => y)
      measurable_id.aemeasurable]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hv, ha]
    have : (R : ℝ) ≠ 0 := by exact_mod_cast hR0
    field_simp
    ring
  -- integrability
  have hcoord : ∀ b r, MemLp (fun Y : Fin B → Fin R → ℝ => Y b r) 2 μ := fun b r =>
    (hin_L2 b r).comp_measurePreserving (hout_eval b)
  have hgmL2 : ∀ b, MemLp (fun Y => groupMean Y b) 2 μ := hG_L2
  have hGM : MemLp (fun Y => grandMean Y) 2 μ := by
    unfold grandMean
    exact (memLp_finsetSum univ (fun b _ => hgmL2 b)).const_mul _
  have hI1 : Integrable (fun Y => ∑ b, (groupMean Y b - grandMean Y) ^ 2) μ :=
    integrable_finsetSum _ (fun b _ => ((hgmL2 b).sub hGM).integrable_sq)
  have hI2 : ∀ b, Integrable (fun Y => ∑ r, (Y b r - groupMean Y b) ^ 2) μ := fun b =>
    integrable_finsetSum _ (fun r _ => ((hcoord b r).sub (hgmL2 b)).integrable_sq)
  have hwithin : ∫ Y, withinV Y ∂μ = ((B : ℝ) * ((R : ℝ) - 1))⁻¹ *
      ∑ b, (R - 1 : ℝ) * v b := by
    unfold withinV
    rw [integral_const_mul, integral_finsetSum _ (fun b _ => hI2 b)]
    simp_rw [hwithin_b]
  have hIW : Integrable (fun Y => withinV Y) μ := by
    unfold withinV
    exact (integrable_finsetSum _ (fun b _ => hI2 b)).const_mul _
  unfold sigmaHatSVB
  rw [integral_const_mul, integral_sub (hI1.const_mul _) (hIW.div_const _),
    integral_const_mul, integral_div, hbetween, hwithin]
  have hB1 : (B : ℝ) - 1 ≠ 0 := by linarith
  have hR1 : (R : ℝ) - 1 ≠ 0 := by linarith
  have hBn : (B : ℝ) ≠ 0 := by linarith
  have hRn : (R : ℝ) ≠ 0 := by linarith
  rw [← Finset.mul_sum, ← Finset.sum_div]
  field_simp
  ring

end SVBLemma1Aux

open SVBLemma1Aux in
theorem solution
    {m B R : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    (ψ : Inputs Ξ → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (n : Fin m → ℕ) (θ : ℝ) (x : Sample Ξ n)
    (hB : 2 ≤ B) (hR : 2 ≤ R) (hθ : 0 < θ ∧ θ ≤ 1)
    (hn : ∀ i, 1 ≤ n i) (hs : ∀ i, 1 ≤ subsampleSize θ n i)
    (hOracle : SimOracle ψ simLaw)
    (hSecond : ∀ I : Resample n (subsampleSize θ n),
      Integrable (fun y => (y - ψ (Fbar univ I x)) ^ 2)
        (simLaw (Fbar univ I x))) :
    (Fintype.card (Fin B → Resample n (subsampleSize θ n)) : ℝ)⁻¹ *
      ∑ I : Fin B → Resample n (subsampleSize θ n),
        ∫ Y, sigmaHatSVB θ Y ∂(outputLaw (R := R) simLaw I x) =
      sigmaSVB ψ θ x := by
  classical
  set s := subsampleSize θ n with hs_def
  have hprobQ : ∀ J : Resample n s, ∀ i, IsProbabilityMeasure (Fbar univ J x i) := by
    intro J i
    simp only [Fbar, Finset.mem_univ, if_true]
    constructor
    simp only [empirical, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, smul_eq_mul]
    have : s i ≠ 0 := by have := hs i; omega
    exact ENNReal.inv_mul_cancel (by exact_mod_cast this) (ENNReal.natCast_ne_top _)
  have hor : ∀ J : Resample n s, IsProbabilityMeasure (simLaw (Fbar univ J x)) ∧
      (∫ y, y ∂(simLaw (Fbar univ J x))) = ψ (Fbar univ J x) := fun J =>
    ⟨(hOracle _ (hprobQ J)).1, (hOracle _ (hprobQ J)).2.2⟩
  have hL2 : ∀ J : Resample n s, MemLp (fun y : ℝ => y) 2 (simLaw (Fbar univ J x)) := by
    intro J
    haveI := (hor J).1
    have h1 : MemLp (fun y : ℝ => y - ψ (Fbar univ J x)) 2 (simLaw (Fbar univ J x)) :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 (hSecond J)
    have h2 := h1.add (memLp_const (ψ (Fbar univ J x)))
    refine h2.ae_eq (Filter.Eventually.of_forall (fun y => ?_))
    simp
  haveI : Nonempty (Resample n s) := by
    refine ⟨fun i j => ⟨0, ?_⟩⟩
    have := hn i; omega
  have hA : ∀ I : Fin B → Resample n s,
      ∫ Y, sigmaHatSVB θ Y ∂(outputLaw (R := R) simLaw I x) =
        θ * ((B - 1 : ℝ)⁻¹ * ∑ b, (ψ (Fbar univ (I b) x) -
          (B : ℝ)⁻¹ * ∑ b', ψ (Fbar univ (I b') x)) ^ 2) := by
    intro I
    haveI : ∀ b, IsProbabilityMeasure (simLaw (Fbar univ (I b) x)) := fun b => (hor (I b)).1
    have := stepA hB hR (fun b => simLaw (Fbar univ (I b) x)) (fun b => hL2 (I b)) θ
    unfold outputLaw
    rw [this]
    simp_rw [fun b => (hor (I b)).2]
  simp_rw [hA]
  rw [← Finset.mul_sum]
  have hB' := stepB (J := Resample n s) hB (fun J => ψ (Fbar univ J x))
  have hsv : sigmaSVB ψ θ x = θ * ((Fintype.card (Resample n s) : ℝ)⁻¹ *
      ∑ J : Resample n s, (ψ (Fbar univ J x) - (Fintype.card (Resample n s) : ℝ)⁻¹ *
        ∑ J' : Resample n s, ψ (Fbar univ J' x)) ^ 2) := by
    unfold sigmaSVB bootAvg
    rfl
  rw [hsv, ← hB']
  ring
