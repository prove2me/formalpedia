-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.derivExists_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:18.101433+00:00
-- url     : https://prove2.me/submissions/71ba15b3-6cc3-4963-9d1e-9da179cd02fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onepCurve_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_mul_of_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_onepCurve


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (h : DerivExistsAllPosStatement) (ε : Fin n → Bool)
    (p : Bool → ℕ) (emb : ∀ s, KG (fun _ : Fin (p s) => true) →* KG ε)
    (hemb : ∀ s, Continuous (emb s))
    (blk : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (p s)) (Fin (p s)) ℂ)
    (hblk : ∀ s X, inK ε X → inK (fun _ : Fin (p s) => true) (blk s X))
    (hsplit : ∀ X (hX : inK ε X) (t : ℝ),
      toMK (emb true (onepCurve _ (hblk true X hX) t)) *
          toMK (emb false (onepCurve _ (hblk false X hX) t)) =
        NormedSpace.exp ((t : ℂ) • X))
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0 := by
  choose dτs hdτs using fun s => h (p s) V (τ.comp (emb s)) (hτ.comp (hemb s))
  refine ⟨(dτs true).comp (blk true) + (dτs false).comp (blk false), fun X hX γ hγ => ?_⟩
  have hγeq : ∀ t, γ t = emb true (onepCurve _ (hblk true X hX) t) *
      emb false (onepCurve _ (hblk false X hX) t) := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (hγ t).trans (hsplit X hX t).symm
  have hd1 := hdτs true (blk true X) (hblk true X hX) (onepCurve _ (hblk true X hX))
    (toMK_onepCurve _ (hblk true X hX))
  have hd2 := hdτs false (blk false X) (hblk false X hX) (onepCurve _ (hblk false X hX))
    (toMK_onepCurve _ (hblk false X hX))
  have hprod := hasDerivAt_mul_of_one hd1 hd2 (by simp [onepCurve_zero]) (by simp [onepCurve_zero])
  have hfun : (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      fun t => (((τ.comp (emb true)) (onepCurve _ (hblk true X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) *
        (((τ.comp (emb false)) (onepCurve _ (hblk false X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
    funext t
    rw [hγeq t, map_mul]
    rfl
  rw [hfun]
  simpa using hprod
end ReciprocityTheory.ChartRestriction.DS.HW
