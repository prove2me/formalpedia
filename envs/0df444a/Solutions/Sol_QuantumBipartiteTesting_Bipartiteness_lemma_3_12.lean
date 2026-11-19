-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:04:49.095836+00:00
-- url     : https://prove2.me/submissions/609b5099-968e-4b81-a41d-305dd4643d25

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_sampling_monomial_comparison
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_9
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_10
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_11
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private def tableExponent {α : Type} [DecidableEq α] (s : Finset α) : α →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

private lemma exponent_support {α : Type} [DecidableEq α] (s : Finset α) :
    (tableExponent s).support = s := by
  ext a
  simp [tableExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]

private lemma exponent_injective {α : Type} [DecidableEq α] :
    Function.Injective (tableExponent (α := α)) := by
  intro s t h
  simpa only [exponent_support] using congrArg Finsupp.support h

private lemma table_monomial {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) :
    TableMonomial T = MvPolynomial.monomial (tableExponent T.val) (1 : ℝ) := by
  simpa only [pow_one, TableMonomial, tableExponent] using
    (MvPolynomial.prod_X_pow (R := ℝ) (fun _ : I × S => 1) T.val)

private lemma canonical_coefficient {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) :
    (CanonicalPolynomial E A out).coeff (tableExponent T.val) = CanonicalCoeff E A out T := by
  unfold CanonicalPolynomial
  rw [MvPolynomial.coeff_sum]
  rw [sum_eq_single T]
  · simp [table_monomial]
  · intro U hU hUT
    have he : tableExponent U.val ≠ tableExponent T.val := by
      intro h
      exact hUT (Subtype.ext (exponent_injective h))
    simp [table_monomial, he]
  · simp

private lemma coefficient_zero {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) (hT : 2*q < T.val.card) :
    CanonicalCoeff E A out T = 0 := by
  have hdegree := (lemma_2_9 E A out).1
  rw [← canonical_coefficient E A out T]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [exponent_support]
  have hsum : (∑ a ∈ T.val, tableExponent T.val a) = T.val.card := by
    simp [tableExponent, Finsupp.indicator_apply]
  rw [hsum]
  exact hdegree.trans_lt hT



private lemma average_sum {α β : Type*} (s : Finset α) (t : Finset β) (f : β → α → ℝ) :
    Average s (fun x => ∑ i ∈ t, f i x) = ∑ i ∈ t, Average s (f i) := by
  unfold Average
  rw [Finset.sum_comm,Finset.sum_div]

private lemma average_smul {α : Type*} (s : Finset α) (c : ℝ) (f : α → ℝ) :
    Average s (fun x => c*f x) = c*Average s f := by
  unfold Average
  rw [← Finset.mul_sum,mul_div_assoc]

private lemma feasible_sum {N colors M l : ℕ} {β : Type*}
    (t : Finset β) (f : β → Finset (ColoredEdge N colors) → ℝ) :
    FeasibleBase N M l (fun F => ∑ i ∈ t, f i F) = ∑ i ∈ t, FeasibleBase N M l (f i) := by
  unfold FeasibleBase MatchingAverage
  simp_rw [average_sum]

private lemma feasible_smul {N colors M l : ℕ} (c : ℝ) (f : Finset (ColoredEdge N colors) → ℝ) :
    FeasibleBase N M l (fun F => c*f F) = c*FeasibleBase N M l f := by
  unfold FeasibleBase MatchingAverage
  simp_rw [average_smul]

private lemma signing_sum {N colors : ℕ} {β : Type*} (s : Signing) (F : Finset (ColoredEdge N colors))
    (t : Finset β) (f : β → (ColoredEdge N colors → Bool) → ℝ) :
    SigningAverage s F (fun b => ∑ i ∈ t, f i b) = ∑ i ∈ t, SigningAverage s F (f i) := by
  cases s <;> simp only [SigningAverage,average_sum]

private lemma signing_smul {N colors : ℕ} (s : Signing) (F : Finset (ColoredEdge N colors))
    (c : ℝ) (f : (ColoredEdge N colors → Bool) → ℝ) :
    SigningAverage s F (fun b => c*f b) = c*SigningAverage s F f := by
  cases s <;> simp only [SigningAverage,average_smul]

private def FeasibleMonomial {N colors : ℕ} (s : Signing) (T : GraphTable N colors) (M l : ℕ) : ℝ :=
  FeasibleBase N M l (fun F : Finset (ColoredEdge N colors) =>
    SigningAverage s F (fun b => ∏ az ∈ T.val, Indicators (LiftOracle (SignedResponse F b)) az))

private lemma acceptance_decomposition {N colors k w q : ℕ}
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing) (M l : ℕ) :
    FeasibleAcceptance E A out s M l =
      ∑ T : GraphTable N colors, CanonicalCoeff E A out T * FeasibleMonomial s T M l := by
  have ha (O : Address N colors → Option (Fin N × Bool)) :
      Accept E A out O = ∑ T : GraphTable N colors,
        CanonicalCoeff E A out T * ∏ az ∈ T.val, Indicators O az := by
    rw [← (lemma_2_9 E A out).2.2 O]
    simp only [CanonicalPolynomial,TableMonomial,map_sum,map_mul,map_prod,eval_C,eval_X]
  unfold FeasibleAcceptance FeasibleMonomial
  simp_rw [ha,signing_sum,signing_smul,feasible_sum,feasible_smul]

private lemma finite_acceptance_error {N colors k w q M l : ℕ}
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing)
    (hv : ValidParameters N M l) (hsmall : 8*q ≤ M/l) :
    |FeasibleAcceptance E A out s M l-FormalAcceptance E A out s M l| ≤
      (∑ T : GraphTable N colors, |CanonicalCoeff E A out T|)*OverflowProbability N M l := by
  rw [acceptance_decomposition]
  unfold FormalAcceptance
  rw [← Finset.sum_sub_distrib]
  have heq (T : GraphTable N colors) :
      CanonicalCoeff E A out T * FeasibleMonomial s T M l -
        CanonicalCoeff E A out T * FormalMonomial s T M l =
        CanonicalCoeff E A out T*(FeasibleMonomial s T M l-FormalMonomial s T M l) := by ring
  simp_rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply sum_le_sum
  intro T hT
  by_cases hsize : T.val.card ≤ 2*q
  · rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact sampling_monomial_comparison M l hv T (by omega) s
  · rw [coefficient_zero E A out T (Nat.lt_of_not_ge hsize)]
    simp

private lemma grid_capacity {N M l q : ℕ} (hv : ValidParameters N M l)
    (hgrid : Grid N M l) (hq : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ)) : 8*q ≤ M/l := by
  have hl : 0 < l := hv.1
  have hR : (Radius N:ℝ) ≤ (N:ℝ)^(2/3:ℝ)/100 := Nat.floor_le (by positivity)
  have hlR : (l:ℝ) ≤ (N:ℝ)^(2/3:ℝ)/100 :=
    (show (l:ℝ) ≤ Radius N by exact_mod_cast hgrid.2.1).trans hR
  have hNpos : 0 < N := by
    by_contra h
    have hn : N = 0 := by omega
    subst N
    norm_num at hlR
    omega
  have hprod : (q:ℝ)*l ≤ (N:ℝ)/100 := by
    calc
      _ ≤ (N:ℝ)^(1/3:ℝ)*((N:ℝ)^(2/3:ℝ)/100) :=
        mul_le_mul hq hlR (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by
        rw [← mul_div_assoc,← Real.rpow_add (Nat.cast_pos.mpr hNpos)]
        norm_num
  apply (Nat.le_div_iff_mul_le hl).mpr
  have hNM : (N:ℝ) ≤ M := by exact_mod_cast hv.2.1
  have hreal : (8:ℝ)*q*l ≤ M := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact_mod_cast hreal

private lemma error_parameters : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ B : ℝ, 0 < B → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ k w q : ℕ, (q : ℝ) ≤ B * LowerBoundScale N →
      ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
      ∀ out : (Address N 3 × Bits k) × Fin w → Bool, ∀ M l : ℕ, Grid N M l →
        (∀ s : Signing, |FeasibleAcceptance E A out s M l - FormalAcceptance E A out s M l| ≤
          Real.exp (C*q*Real.log N - c*(N : ℝ)^(1/3 : ℝ))) ∧
        FeasibleGap E A out M l = FormalGap E A out M l + GapError E A out M l ∧
        |GapError E A out M l| ≤ 2*Real.exp (C*q*Real.log N - c*(N : ℝ)^(1/3 : ℝ)) := by
  obtain ⟨C,hC,hcoef⟩ := lemma_2_10.2 6 2
  obtain ⟨c,hc,N₁,hN₁⟩ := lemma_3_11
  refine ⟨C,c,hC,hc,?_⟩
  intro B hB
  refine ⟨max (max N₁ 2) ⌈Real.exp B⌉₊,?_⟩
  intro N hN k w q hq E A out M l hgrid
  have hN2 : 2 ≤ N := by omega
  have hExp : Real.exp B ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (le_trans (le_max_right _ _) hN))
  have hlog : B ≤ Real.log (N:ℝ) := by
    calc
      _ = Real.log (Real.exp B) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hExp
  have hlogpos : 0 < Real.log (N:ℝ) := hB.trans_le hlog
  have hqN : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := by
    apply hq.trans
    unfold LowerBoundScale
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogpos).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog
      (Real.rpow_nonneg (Nat.cast_nonneg N) (1/3:ℝ))
  obtain ⟨hv,hover⟩ := hN₁ N (by omega) M l hgrid
  have hcapacity := grid_capacity hv hgrid hqN
  have hcoef' := hcoef N hN2 (Address N 3) (Fin N × Bool)
    (by simp only [Address,Fintype.card_prod,Fintype.card_option,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; omega) k w q E A out
  have hover0 : 0 ≤ OverflowProbability N M l := by
    unfold OverflowProbability Average
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply sum_nonneg
    intro b hb
    split_ifs <;> norm_num
  have hsingle (s : Signing) : |FeasibleAcceptance E A out s M l - FormalAcceptance E A out s M l| ≤
      Real.exp (C*q*Real.log N-c*(N:ℝ)^(1/3:ℝ)) := by
    apply (finite_acceptance_error E A out s hv hcapacity).trans
    apply (mul_le_mul hcoef' hover hover0 (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hsingle,?_,?_⟩
  · unfold GapError
    ring
  · have hh := abs_sub_le (FeasibleAcceptance E A out .yes M l-FormalAcceptance E A out .yes M l) 0
      (FeasibleAcceptance E A out .no M l-FormalAcceptance E A out .no M l)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have heq : GapError E A out M l =
        (FeasibleAcceptance E A out .yes M l-FormalAcceptance E A out .yes M l)-
        (FeasibleAcceptance E A out .no M l-FormalAcceptance E A out .no M l) := by
      unfold GapError FeasibleGap FormalGap
      ring
    rw [heq]
    linarith [hsingle .yes,hsingle .no]

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness
open Finset Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    (∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ B : ℝ, 0 < B → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ k w q : ℕ, (q : ℝ) ≤ B * LowerBoundScale N →
      ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
      ∀ out : (Address N 3 × Bits k) × Fin w → Bool, ∀ M l : ℕ, Grid N M l →
        (∀ s : Signing, |FeasibleAcceptance E A out s M l - FormalAcceptance E A out s M l| ≤
          Real.exp (C₁*q*Real.log N - c₁*(N : ℝ)^(1/3 : ℝ))) ∧
        FeasibleGap E A out M l = FormalGap E A out M l + GapError E A out M l ∧
        |GapError E A out M l| ≤ 2*Real.exp (C₁*q*Real.log N - c₁*(N : ℝ)^(1/3 : ℝ))) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ UniformGapVanishing c₀) := by
  obtain ⟨C,c,hC,hc,hall⟩ := error_parameters
  refine ⟨⟨C,c,hC,hc,hall⟩,?_⟩
  let c₀ := c/(2*C)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀,hc₀,?_⟩
  intro δ hδ
  have hp : Tendsto (fun N : ℕ => (N:ℝ)^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun N : ℕ => -(c/2)*(N:ℝ)^(1/3:ℝ)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -(c/2) < 0)).mpr hp
  have he : Tendsto (fun N : ℕ => 2*Real.exp (-(c/2)*(N:ℝ)^(1/3:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hn))
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds hδ))
  obtain ⟨N₂,hN₂⟩ := hall c₀ hc₀
  refine ⟨max (max N₁ N₂) 2,?_⟩
  intro N hN k w q hq E A out M l hgrid
  have hN2 : 2 ≤ N := by omega
  have herr := (hN₂ N (by omega) k w q hq E A out M l hgrid).2.2
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqlog : (q:ℝ)*Real.log N ≤ c₀*(N:ℝ)^(1/3:ℝ) := by
    unfold LowerBoundScale at hq
    have hh := (le_div_iff₀ hlog).mp (show (q:ℝ) ≤ c₀*(N:ℝ)^(1/3:ℝ)/Real.log N by
      simpa only [mul_div_assoc] using hq)
    exact hh
  have hcprod : C*c₀ = c/2 := by dsimp [c₀]; field_simp
  have hexp : C*q*Real.log N-c*(N:ℝ)^(1/3:ℝ) ≤ -(c/2)*(N:ℝ)^(1/3:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hqlog hC.le
    rw [show C*(c₀*(N:ℝ)^(1/3:ℝ)) = (c/2)*(N:ℝ)^(1/3:ℝ) by rw [← mul_assoc,hcprod]] at hh
    nlinarith
  apply herr.trans
  apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num : (0:ℝ) ≤ 2))
  exact (hN₁ N (by omega)).le
end
