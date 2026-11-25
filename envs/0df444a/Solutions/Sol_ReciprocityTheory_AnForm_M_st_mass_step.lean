-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mass_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:30.279008+00:00
-- url     : https://prove2.me/submissions/0f73b39a-ccc4-4d3b-9612-41ef63d2324d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_stokes_of
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntSymm
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : PartsStatement) [CompactSpace X] [T2Space X] {n : ℕ}
    (A : FinHolAtlas (n + 1) X) (Ψ : Fin (n + 1) → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i))
    (i0 : Fin (n + 1)) (u : X → ℝ) (hu : A.Smooth u) :
    mInt A (Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u)) (fun _ => 1) =
      mInt A Ψ (fun _ => 1) := by
  classical
  set Ψ' := Function.update Ψ i0 (Ψ i0 + LocPot.ofFun u) with hΨ'
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i0
  have hne : ∀ i : Fin n, σ i.succ ≠ i0 := by
    intro i h
    have h2 := congrArg σ h
    simp only [σ, Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
    exact Fin.succ_ne_zero i h2
  set Φ' : Fin n → LocPot X := fun i => Ψ (σ i.succ) with hΦ'
  have h1 : Ψ' ∘ σ = Fin.cons (Ψ i0 + LocPot.ofFun u) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ, Ψ']
    · simp only [Function.comp, Fin.cons_succ, Φ', Ψ']
      rw [Function.update_of_ne (hne i)]
  have h2 : Ψ ∘ σ = Fin.cons (Ψ i0) Φ' := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [σ]
    · simp [Φ']
  have hPot' : ∀ i, IsPotential A (Φ' i) := fun i => hΨ _
  have hu' := isPotential_ofFun A u hu
  have hint : ∀ Q : LocPot X, IsPotential A Q → MIntegrable A (Fin.cons Q Φ') (fun _ => 1) := by
    intro Q hQ
    refine mIntegrableCont A _ ?_ _ continuous_const
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hQ
    · simpa using hPot' i
  rw [← mIntSymm A Ψ' σ, h1, mIntAdd A _ _ Φ' (hΨ i0) hu' hPot' _ (hint _ (hΨ i0)) (hint _ hu'),
    st_stokes_of hP A u hu Φ' hPot', add_zero, ← h2, mIntSymm]
end ReciprocityTheory.AnForm.M
