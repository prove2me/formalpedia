-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_colon_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:36.695216+00:00
-- url     : https://prove2.me/submissions/0a8a8844-b925-4563-8806-9cf5a0b04939

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MultAtEqCount
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Ideal (MRing ι)} {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)}
    {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)} (h0 : F 0 = J)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) (j : Fin N) : J ≤ q j := by

  have mono : ∀ k : ℕ, ∀ hk : k ≤ N, J ≤ F ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have e : (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [e, h0]
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have step := (hj ⟨k, hk'⟩).1
      calc J ≤ F (Fin.castSucc ⟨k, hk'⟩) := ih hk'.le
        _ ≤ F (Fin.castSucc ⟨k, hk'⟩) ⊔ Ideal.span {f ⟨k, hk'⟩} := le_sup_left
        _ = F (Fin.succ ⟨k, hk'⟩) := step.symm
  intro g hg
  exact ((hj j).2 g).2 (Ideal.mul_mem_right _ _ (mono j.val j.isLt.le hg))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
