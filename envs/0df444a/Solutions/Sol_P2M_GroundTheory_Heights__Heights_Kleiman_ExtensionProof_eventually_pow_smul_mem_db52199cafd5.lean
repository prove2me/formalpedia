-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:36.611839+00:00
-- url     : https://prove2.me/submissions/876ac871-ff43-4837-a699-77d2ab3727aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution (F : SubFamily S x E) {i : Fin (N + 1)} (hi : x i ≠ 0) {y : E}
    (hy : y ∈ F.sub (singleChart hi)) (J : Chart x) :
    ∀ᶠ n : ℕ in Filter.atTop, x i ^ n • y ∈ (F.twist (twistSys S x (n : ℤ))).sub J := by
  classical
  obtain ⟨j, hj⟩ := J.2.1
  have hxj : x j ≠ 0 := (mem_support x).mp (J.2.2 hj)
  let K : Chart x := ⟨insert i J.1, Finset.insert_nonempty _ _,
    Finset.insert_subset ((mem_support x).mpr hi) J.2.2⟩
  have hJK : J.1 ⊆ K.1 := Finset.subset_insert _ _
  have hiK : (singleChart hi).1 ⊆ K.1 := by
    simp [singleChart, K]
  have hyK : y ∈ F.sub K := F.mono _ _ hiK y hy
  obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff J K hJK y).mp hyK
  have hinv : (a : Ω) * ((↑u⁻¹ : chartRing S x K) : Ω) = 1 := by
    have := congrArg Subtype.val (Units.mul_inv u)
    rw [hu] at this
    exact this
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := (↑u⁻¹ : chartRing S x K).2
  rw [hb] at hinv
  obtain ⟨p, t, ht, rfl⟩ := monos_insert_decomp hs
  obtain ⟨q, hq⟩ := monos_isHomogeneous ht
  have hs0 := eval_ne_zero_of_mem_monos K hs
  have hX : X i ^ p * t ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hepq : e = p + q := hse.inj_right ((isHomogeneous_X_pow i p).mul hq) hX
  subst hepq
  have ht0 : aeval x t ≠ 0 := eval_ne_zero_of_mem_monos J ht
  rw [map_mul, map_pow, aeval_X] at hinv
  have key : (a : Ω) * aeval x f = x i ^ p * aeval x t := by
    have h1 : x i ^ p * aeval x t ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) ht0
    field_simp at hinv
    linear_combination hinv
  refine Filter.eventually_atTop.mpr ⟨p, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdeg : (t * X j ^ (p + k)).IsHomogeneous (p + q + k) := by
    have := hq.mul (isHomogeneous_X_pow j (p + k))
    rwa [show q + (p + k) = p + q + k by ring] at this
  have hc : aeval x f * x i ^ k / (aeval x t * x j ^ (p + k)) ∈ chartRing S x J :=
    ⟨f * X i ^ k, t * X j ^ (p + k), p + q + k, mul_mem ht (pow_mem (X_mem_monos hj) _),
      hf.mul (isHomogeneous_X_pow i k), hdeg, by simp [map_mul, map_pow, aeval_X]⟩
  have hxy : x i ^ (p + k) • y =
      x j ^ (p + k) • ((⟨_, hc⟩ : chartRing S x J) • ((a : Ω) • y)) := by
    rw [Subalgebra.smul_def, smul_smul, smul_smul]
    congr 1
    field_simp
    linear_combination (-(x i ^ k)) * key
  rw [hxy]
  refine Submodule.subset_span ⟨x j ^ (p + k), ?_, _, Submodule.smul_mem _ _ hay, rfl⟩
  exact Submodule.subset_span ⟨X j ^ (p + k), 1, 0, p + k, one_mem _, isHomogeneous_X_pow j _,
    isHomogeneous_one _ _, by simp, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
