-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:46.429696+00:00
-- url     : https://prove2.me/submissions/e42e1a01-fb92-4084-ae08-1beb646945ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_prod_intertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    {n k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (D : Fin k → Fin k → Module.End ℂ R')
    (ι : Fin k → Fin n) (hι : Function.Injective ι) (l : M →ₗ[ℂ] R')
    (hl : ∀ i j, l ∘ₗ E (ι i) (ι j) = D i j ∘ₗ l) {p : ℕ} (Rw Cw : Fin p → Fin k) (x : ℂ) :
    l ∘ₗ cminor E (ι ∘ Rw) (ι ∘ Cw) x = cminor D Rw Cw x ∘ₗ l := by
  have hc : ∀ (y : ℂ) (a b : Fin k), l ∘ₗ capEntry E y (ι a) (ι b) = capEntry D y a b ∘ₗ l := by
    intro y a b
    have hv : ∀ v, l (E (ι a) (ι b) v) = D a b (l v) := fun v => LinearMap.congr_fun (hl a b) v
    unfold capEntry
    simp only [hι.eq_iff]
    ext v
    split_ifs <;> simp [hv]
  have key : ∀ σ : Equiv.Perm (Fin p),
      l ∘ₗ (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) ((ι ∘ Rw) (σ j)) ((ι ∘ Cw) j)).prod =
        (List.ofFn fun j : Fin p => capEntry D (x - ((j : ℕ) : ℂ)) (Rw (σ j)) (Cw j)).prod ∘ₗ l := by
    intro σ
    apply basic_prod_intertwine
    intro j
    exact hc _ _ _
  unfold cminor
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := LinearMap.congr_fun (key σ) v
  simp only [LinearMap.comp_apply] at h1
  first
  | (rw [LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h1])
  | simp [h1, map_zsmul]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
