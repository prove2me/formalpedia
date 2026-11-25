-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_comap_wwIdeal_yyEmb_f63c049915a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:31.155935+00:00
-- url     : https://prove2.me/submissions/8ba90f75-d936-4c32-90ae-512c94d6afae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.wwIdeal x δ e φ (a 0) (a 1)).comap
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      T.yyIdeal x δ e φ (a j) := by
  ext f
  rw [Ideal.mem_comap, T.wwIdeal, T.yyIdeal, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply,
    multiConeMap_ww_comp_yyEmb, RingHom.comp_apply]
  exact map_eq_zero_iff _ (rename_injective _ (segreBlockEmbedding_injective j))
end GroundTheory.Heights₂.Heights.Inter
