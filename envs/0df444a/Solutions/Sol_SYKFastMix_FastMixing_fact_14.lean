-- Prove2me | solution 1 for SYKFastMix.FastMixing.fact_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:26:06.847456+00:00
-- url     : https://prove2.me/submissions/0a384b9a-07af-4360-9bd0-ecc3d00399f9

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Theorems.Thm_MatrixTail_Gaussian_theorem4_1

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexOrder
namespace SYKFastMix.FastMixing

lemma rawString_hermitian_of_card_four {N : ℕ} (Q : Model N)
    (S : Finset (Fin N)) (hS : S.card = 4) : (rawString Q S).IsHermitian := by
  unfold rawString Matrix.IsHermitian
  rw [Matrix.conjTranspose_list_prod]
  have hlen : (S.sort (· ≤ ·)).length = 4 := by simpa using hS
  have hnodup : (S.sort (· ≤ ·)).Nodup := S.sort_nodup (· ≤ ·)
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  rw [hlist] at hnodup
  simp at hnodup
  rcases hnodup with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  rw [hlist]
  simp
  rw [(Q.car.herm a).eq, (Q.car.herm b).eq, (Q.car.herm c).eq, (Q.car.herm d).eq]
  calc
    Q.γ d * (Q.γ c * (Q.γ b * Q.γ a)) =
        (Q.γ d * Q.γ c) * (Q.γ b * Q.γ a) := by noncomm_ring
    _ = -(Q.γ c * Q.γ d) * (Q.γ b * Q.γ a) := by
          rw [Q.car.anticomm d c (Ne.symm hcd)]
    _ = Q.γ c * (-(Q.γ d * Q.γ b) * Q.γ a) := by noncomm_ring
    _ = Q.γ c * (Q.γ b * Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm d b (Ne.symm hbd)]
          noncomm_ring
    _ = (Q.γ c * Q.γ b) * (Q.γ d * Q.γ a) := by noncomm_ring
    _ = -(Q.γ b * Q.γ c) * (Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm c b (Ne.symm hbc)]
    _ = Q.γ b * Q.γ c * (Q.γ a * Q.γ d) := by
          rw [Q.car.anticomm d a (Ne.symm had)]
          noncomm_ring
    _ = Q.γ b * (Q.γ c * Q.γ a) * Q.γ d := by noncomm_ring
    _ = -(Q.γ b * (Q.γ a * Q.γ c) * Q.γ d) := by
          rw [Q.car.anticomm c a (Ne.symm hac)]
          noncomm_ring
    _ = -((Q.γ b * Q.γ a) * (Q.γ c * Q.γ d)) := by noncomm_ring
    _ = (Q.γ a * Q.γ b) * (Q.γ c * Q.γ d) := by
          rw [Q.car.anticomm b a (Ne.symm hab)]
          noncomm_ring
    _ = Q.γ a * (Q.γ b * (Q.γ c * Q.γ d)) := by noncomm_ring

lemma hamiltonian_hermitian {N : ℕ} (Q : Model N) (w : Disorder N) :
    (hamiltonian Q w).IsHermitian := by
  unfold hamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Matrix.conjTranspose_smul, (rawString_hermitian_of_card_four Q A.1 A.2).eq]
  simp

end SYKFastMix.FastMixing


namespace SYKFastMix.FastMixing

lemma rawString_unitary {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    rawString Q S ∈ unitary (Mat (SiteHilbert N)) := by
  unfold rawString
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  apply Unitary.mem_iff.mpr
  change (Q.γ i)ᴴ * Q.γ i = 1 ∧ Q.γ i * (Q.γ i)ᴴ = 1
  rw [(Q.car.herm i).eq]
  exact ⟨Q.car.sq i, Q.car.sq i⟩

lemma rawString_sq {N : ℕ} (Q : Model N) (A : SYKEdge.KSet N 4) :
    rawString Q A.1 ^ 2 = 1 := by
  have h := Unitary.star_mul_self_of_mem (rawString_unitary Q A.1)
  change (rawString Q A.1)ᴴ * rawString Q A.1 = 1 at h
  rw [(rawString_hermitian_of_card_four Q A.1 A.2).eq] at h
  simpa only [pow_two] using h

lemma disorder_coordinate_standard {N : ℕ} (Q : Model N) :
    let v := Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3)
    let σ := Real.sqrt (v : ℝ)
    ∀ A : SYKEdge.KSet N 4,
      (disorderLaw Q).map (fun w ↦ w A / σ) = gaussianReal 0 1 := by
  dsimp only
  intro A
  have hJ := Q.positive
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) Q.size)
  have hv : 0 < 6 * Q.J^2 / (N : ℝ)^3 := by positivity
  have hv' : 0 < (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ) := by
    rwa [Real.coe_toNNReal _ hv.le]
  rw [show (fun w : Disorder N ↦ w A / Real.sqrt (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ)) =
      (fun x : ℝ ↦ x / Real.sqrt (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ)) ∘ Function.eval A from rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [disorderLaw, (measurePreserving_eval _ A).map_eq, gaussianReal_map_div_const]
  simp only [zero_div]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
  rw [Real.sq_sqrt hv'.le, div_self hv'.ne']

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

lemma hamiltonian_gaussian_tail {N : ℕ} (Q : Model N) (t : ℝ) (ht : 0 ≤ t) :
    (disorderLaw Q).real {w | t ≤ SYKEdge.opNorm (hamiltonian Q w)} ≤
      2 * (2^(N/2) : ℝ) * Real.exp (-t^2 /
        (2 * ((Fintype.card (SYKEdge.KSet N 4) : ℝ) * (6 * Q.J^2 / (N : ℝ)^3)))) := by
  let v := Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3)
  let σ := Real.sqrt (v : ℝ)
  let e := (Fintype.equivFin (SYKEdge.KSet N 4)).symm
  let B : Fin (Fintype.card (SYKEdge.KSet N 4)) → Mat (SiteHilbert N) :=
    fun k ↦ σ • rawString Q (e k).1
  let ξ : Fin (Fintype.card (SYKEdge.KSet N 4)) → Disorder N → ℝ := fun k w ↦ w (e k) / σ
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have hJ := Q.positive
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) Q.size)
  have hv : 0 < 6 * Q.J^2 / (N : ℝ)^3 := by positivity
  have hσ : 0 < σ := by
    change 0 < Real.sqrt (v : ℝ)
    apply Real.sqrt_pos.mpr
    change 0 < (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ)
    rwa [Real.coe_toNNReal _ hv.le]
  have hσsq : σ^2 = 6 * Q.J^2 / (N : ℝ)^3 := by
    change Real.sqrt (v : ℝ)^2 = _
    rw [Real.sq_sqrt (NNReal.coe_nonneg _)]
    exact Real.coe_toNNReal _ hv.le
  have hB : ∀ k, (B k).IsHermitian := fun k ↦
    (rawString_hermitian_of_card_four Q (e k).1 (e k).2).smul (IsSelfAdjoint.all σ)
  have hind : iIndepFun ξ (disorderLaw Q) := by
    have h0 : iIndepFun (fun A (w : Disorder N) ↦ w A / σ) (disorderLaw Q) :=
      iIndepFun_pi (fun _ ↦ (measurable_id.div_const σ).aemeasurable)
    exact h0.precomp e.injective
  have hlaw : ∀ k, MatrixTail.Gaussian.IsStdGaussian (disorderLaw Q) (ξ k) := by
    intro k
    refine ⟨by dsimp [ξ]; fun_prop, ?_⟩
    exact disorder_coordinate_standard Q (e k)
  have hsum (w : Disorder N) : ∑ k, ξ k w • B k = hamiltonian Q w := by
    calc
      ∑ k, ξ k w • B k = ∑ k, (w (e k) : ℂ) • rawString Q (e k).1 := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [ξ, B]
        rw [smul_smul, div_mul_cancel₀ _ hσ.ne']
      _ = _ := e.sum_comp (fun A ↦ (w A : ℂ) • rawString Q A.1)
  have hvar : MatrixTail.Gaussian.specNorm (∑ k, B k ^ 2) =
      (Fintype.card (SYKEdge.KSet N 4) : ℝ) * (6 * Q.J^2 / (N : ℝ)^3) := by
    have hBs (k) : B k ^ 2 = σ^2 • (1 : Mat (SiteHilbert N)) := by
      dsimp [B]
      rw [smul_pow, rawString_sq]
    simp_rw [hBs]
    rw [← Finset.sum_smul]
    change ‖((∑ _ : Fin (Fintype.card (SYKEdge.KSet N 4)), σ^2) • (1 : Mat (SiteHilbert N)))‖ = _
    rw [norm_smul, norm_one, mul_one, Real.norm_of_nonneg (by positivity)]
    simp [hσsq]
  have h := (MatrixTail.Gaussian.theorem4_1 (disorderLaw Q) B hB ξ hind (Or.inl hlaw) t ht).2
  rw [hvar] at h
  simpa only [hsum, MatrixTail.Gaussian.specNorm, SYKEdge.opNorm, Nat.cast_pow, Nat.cast_ofNat] using h

theorem solution {N : ℕ} (Q : Model N) :
  MeasurableSet {w | SYKEdge.opNorm (hamiltonian Q w) > 2 * Q.J * N} ∧
  disorderLaw Q {w | SYKEdge.opNorm (hamiltonian Q w) > 2 * Q.J * N} ≤
    ENNReal.ofReal (Real.rpow 2 (-(5 * (N : ℝ) / 2))) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have hJ := Q.positive
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) Q.size)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast Q.size
  have hcont : Continuous (hamiltonian Q) := by unfold hamiltonian; fun_prop
  have hnorm : Continuous (fun w ↦ SYKEdge.opNorm (hamiltonian Q w)) := by
    change Continuous (fun w ↦ ‖hamiltonian Q w‖)
    exact hcont.norm
  refine ⟨measurableSet_lt measurable_const hnorm.measurable, ?_⟩
  have hcard : Fintype.card (SYKEdge.KSet N 4) = N.choose 4 := by
    simp [SYKEdge.KSet]
  have hcardpos : 0 < (Fintype.card (SYKEdge.KSet N 4) : ℝ) := by
    rw [hcard]
    exact_mod_cast Nat.choose_pos Q.size
  have hcardle : (Fintype.card (SYKEdge.KSet N 4) : ℝ) ≤ (N : ℝ)^4 / 24 := by
    rw [hcard]
    have h := (Nat.choose_le_pow_div 4 N : (N.choose 4 : ℝ) ≤ (N : ℝ)^4 / (4:ℕ).factorial)
    norm_num [Nat.factorial] at h
    exact h
  let V : ℝ := (Fintype.card (SYKEdge.KSet N 4) : ℝ) * (6 * Q.J^2 / (N : ℝ)^3)
  have hV : 0 < V := by dsimp [V]; positivity
  have hVle : V ≤ Q.J^2 * N / 4 := by
    calc
      V ≤ ((N : ℝ)^4 / 24) * (6 * Q.J^2 / (N : ℝ)^3) :=
        mul_le_mul_of_nonneg_right hcardle (by positivity)
      _ = _ := by field_simp; ring
  have he : -(2 * Q.J * N)^2 / (2 * V) ≤ -8 * (N : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*V)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hVle (show 0 ≤ 16 * (N : ℝ) by positivity)]
  have htail := hamiltonian_gaussian_tail Q (2 * Q.J * N) (by positivity)
  change (disorderLaw Q).real {w | 2 * Q.J * N ≤ SYKEdge.opNorm (hamiltonian Q w)} ≤
    2 * (2^(N/2) : ℝ) * Real.exp (-(2 * Q.J * N)^2 / (2 * V)) at htail
  have hbound : 2 * (2^(N/2) : ℝ) * Real.exp (-8 * (N : ℝ)) ≤
      Real.rpow 2 (-(5 * (N : ℝ) / 2)) := by
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog1 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at h
      exact h
    have hhalf : (N / 2 : ℕ) ≤ (N : ℝ) / 2 := by
      have hn := Nat.div_mul_le_self N 2
      exact (le_div_iff₀ (by norm_num)).mpr (by exact_mod_cast hn)
    calc
      2 * (2^(N/2) : ℝ) * Real.exp (-8 * (N : ℝ)) =
          Real.exp (Real.log 2 + (N/2 : ℕ) * Real.log 2 + -8 * (N : ℝ)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (Real.log 2 * (-(5 * (N : ℝ) / 2))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hhalf hlog0,
          mul_le_mul_of_nonneg_left hlog1 hN.le]
      _ = Real.rpow 2 (-(5 * (N : ℝ) / 2)) :=
        (Real.rpow_def_of_pos (by norm_num) _).symm
  have hreal : (disorderLaw Q).real {w | 2 * Q.J * N < SYKEdge.opNorm (hamiltonian Q w)} ≤
      Real.rpow 2 (-(5 * (N : ℝ) / 2)) := by
    calc
      _ ≤ (disorderLaw Q).real {w | 2 * Q.J * N ≤ SYKEdge.opNorm (hamiltonian Q w)} :=
        measureReal_mono fun w hw ↦ (show 2 * Q.J * N < SYKEdge.opNorm (hamiltonian Q w) from hw).le
      _ ≤ _ := htail
      _ ≤ 2 * (2^(N/2) : ℝ) * Real.exp (-8 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
      _ ≤ _ := hbound
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal


