-- Prove2me | solution 1 for StableMSR.Recovery.validLabels_feasible
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:32:40.812239+00:00
-- url     : https://prove2.me/submissions/89524b4e-806e-4af3-af9b-3c948a27c079

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace OutputDecodingAux

/-- Fibres of a surjective, range-checked integer labelling form an exact partition. -/
theorem feasible_of_integer_labels {n k : ℕ} (label : Point n → ℤ)
    (hrange : ∀ x, 0 ≤ label x ∧ label x < (k : ℤ))
    (hsurj : ∀ j : Fin k, ∃ x, label x = (j.val : ℤ)) :
    Feasible Finset.univ k
      ((Finset.univ : Finset (Fin k)).image (fun j =>
        (Finset.univ : Cluster n).filter (fun x => label x = (j.val : ℤ)))) := by
  classical
  let B : Fin k → Cluster n := fun j => Finset.univ.filter (fun x => label x = (j.val : ℤ))
  have hBne : ∀ j, (B j).Nonempty := by
    intro j
    obtain ⟨x, hx⟩ := hsurj j
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  have hBinj : Function.Injective B := by
    intro i j hij
    obtain ⟨x, hx⟩ := hBne i
    have hxi : label x = (i.val : ℤ) := (Finset.mem_filter.mp hx).2
    have hxjmem : x ∈ B j := hij ▸ hx
    have hxj : label x = (j.val : ℤ) := (Finset.mem_filter.mp hxjmem).2
    apply Fin.ext
    omega
  change Feasible Finset.univ k (Finset.univ.image B)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hBinj]
    simp
  · intro C hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
    exact hBne j
  · intro C hC D hD hCD
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi : label x = (i.val : ℤ) := (Finset.mem_filter.mp hxi).2
    have hj : label x = (j.val : ℤ) := (Finset.mem_filter.mp hxj).2
    have hij : i = j := by apply Fin.ext; omega
    exact hCD (congrArg B hij)
  · apply Finset.eq_univ_of_forall
    intro x
    have hnonneg := (hrange x).1
    have hlt := (hrange x).2
    let j : Fin k := ⟨(label x).toNat, by omega⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨B j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change label x = ((label x).toNat : ℤ)
    omega

end OutputDecodingAux


/-- Valid machine-output labels already imply the feasibility part of recovery. -/
theorem solution {n k : ℕ} (s : MinSumFPT.State)
    (h : ValidLabels n k s) : Feasible Finset.univ k (outputPartition n k s) := by
  exact OutputDecodingAux.feasible_of_integer_labels
    (fun x => s.imem (-1 - (x.val : ℤ))) h.1 h.2

