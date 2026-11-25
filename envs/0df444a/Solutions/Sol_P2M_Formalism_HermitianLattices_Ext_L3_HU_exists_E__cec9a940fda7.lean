-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:26.597455+00:00
-- url     : https://prove2.me/submissions/3cfbbe60-7a6a-470b-8f93-fbd6e9f95bb2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_pow_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_common_den
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_E
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_isUnif0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_gramK_eq_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_jK_inj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0)
    (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) :
    ∃ (E₀ : Matrix κ κ (𝓞 K)) (d : 𝓞 F), d ∉ 𝔭 ^ (e + 1) ∧ H * E₀ = ι d • (1 : Matrix κ κ (𝓞 K)) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨t, ht, hz⟩ := exists_common_den (fun p : κ × κ => E p.1 p.2) (fun p => hE p.1 p.2)
  choose z hz using hz
  refine ⟨Matrix.of fun i j => z (i, j), t * π₀ ^ e, ?_, ?_⟩
  · have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) (i := 0) (by rwa [zero_add, pow_one]) (pow_notMem h𝔭 hu.notMem e)
    rwa [zero_add] at this
  · have h1 : (Matrix.of fun i j => z (i, j)).map jK = jK (ι t) • E := by
      ext i j
      exact hz (i, j)
    have h2 : (H * Matrix.of fun i j => z (i, j)).map jK = (ι (t * π₀ ^ e) • (1 : Matrix κ κ (𝓞 K))).map jK := by
      rw [Matrix.map_mul, h1, ← gramK_eq_map hH, Matrix.mul_smul, hHE, smul_smul]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    exact Matrix.ext fun i j => jK_inj (congrFun (congrFun h2 i) j)
end Formalism.HermitianLattices.Ext.L3.HU
