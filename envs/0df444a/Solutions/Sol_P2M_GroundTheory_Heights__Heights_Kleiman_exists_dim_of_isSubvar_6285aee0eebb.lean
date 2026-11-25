-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_dim_of_isSubvar_6285aee0eebb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:46.101798+00:00
-- url     : https://prove2.me/submissions/a5f0cd65-1287-4adb-9006-899fce76d384

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2


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
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {pp : Ideal (Poly k N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ D : ℕ, IsSubvar x (primeOf (S := k) x) D := by
  have hup : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    have h1 := ringKrullDim_le_of_surjective (Ideal.Quotient.mk (primeOf (S := k) x))
      Ideal.Quotient.mk_surjective
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1
  have hlo : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) := by
    rw [← hW.dim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.le) (Ideal.Quotient.factor_surjective hW.le)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (Poly k N ⧸ primeOf (S := k) x) = (n : WithBot ℕ∞) := by
    generalize ringKrullDim (Poly k N ⧸ primeOf (S := k) x) = d at hup hlo ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hlo (by simp)
    | coe m =>
      induction m using ENat.recTopCoe with
      | top =>
        exfalso
        have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := hup
        exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
      | coe n => exact ⟨n, rfl⟩
  rw [hn] at hlo
  have hle : e + 1 ≤ n := by exact_mod_cast hlo
  obtain ⟨i, hi⟩ := hW.relevant
  refine ⟨n - 1, ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf x hp d, le_rfl,
    ⟨i, fun h => hi (hW.le h)⟩, ?_⟩⟩
  rw [hn, Nat.sub_add_cancel (by omega)]
end GroundTheory.Heights₂.Heights.Kleiman
