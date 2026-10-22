-- Prove2me | solution 1 for StrategicAlloc.CutChoose.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:44:23.750677+00:00
-- url     : https://prove2.me/submissions/8c482d84-251e-4843-b994-64b340e539b0

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

set_option autoImplicit false
open StrategicAlloc.CutChoose

theorem solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : StrategicAlloc.RRFair.IsAllocation A)
    (hmms : IsApproxMMS 1 v A) :
    IsEFX v A := by
  intro i j _ g hg hvg
  by_cases hij : i = j
  · subst hij
    unfold StrategicAlloc.RRFair.val
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun h _ _ => hv i h)
  · by_contra hcon
    push_neg at hcon
    have hdis : Disjoint (A i) (A j) := hA.1 hij
    have hgi : g ∉ A i := fun h => Finset.disjoint_left.mp hdis h hg
    have hji : j ≠ i := Ne.symm hij
    let E : Finset (Fin m) := (A j).erase g
    let f : Fin m → Fin 2 := fun h => if h ∈ E then j else i
    have hvalnn : ∀ S : Finset (Fin m), 0 ≤ StrategicAlloc.RRFair.val v i S := fun S =>
      Finset.sum_nonneg (fun h _ => hv i h)
    -- the bundle of the second part of the partition has value at least v_i(A_i) + v_i(g)
    have hrest : StrategicAlloc.RRFair.val v i (A i) + v i g ≤
        StrategicAlloc.RRFair.val v i (Finset.univ.filter (fun h => f h = i)) := by
      have hsub : insert g (A i) ⊆ Finset.univ.filter (fun h => f h = i) := by
        intro h hh
        rw [Finset.mem_insert] at hh
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
        have hnot : h ∉ E := by
          rcases hh with rfl | hh
          · simp [E]
          · intro hE
            exact Finset.disjoint_left.mp hdis hh (Finset.mem_of_mem_erase hE)
        simp [hnot]
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => hv i h)
      unfold StrategicAlloc.RRFair.val at this ⊢
      rw [Finset.sum_insert hgi] at this
      linarith
    have hE : Finset.univ.filter (fun h => f h = j) = E := by
      ext h
      by_cases hh : h ∈ E <;> simp [f, hh, hij]
    have hbound : ∀ k : Fin 2,
        min (StrategicAlloc.RRFair.val v i E) (StrategicAlloc.RRFair.val v i (A i) + v i g) ≤
          StrategicAlloc.RRFair.val v i (Finset.univ.filter (fun h => f h = k)) := by
      intro k
      by_cases hk : k = j
      · subst hk
        rw [hE]
        exact min_le_left _ _
      · have hki : k = i := by
          apply Fin.ext
          have h1 := k.isLt
          have h2 := i.isLt
          have h3 := j.isLt
          have h4 : k.val ≠ j.val := fun h => hk (Fin.ext h)
          have h5 : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega
        subst hki
        exact (min_le_right _ _).trans hrest
    have hmu : min (StrategicAlloc.RRFair.val v i E)
        (StrategicAlloc.RRFair.val v i (A i) + v i g) ≤ mu v i := by
      unfold mu LittleCharity.MMS.mms
      refine le_ciSup_of_le (Set.finite_range _).bddAbove f ?_
      refine le_ciInf (fun k => ?_)
      convert hbound k
    have h1 := hmms i
    have h2 : StrategicAlloc.RRFair.val v i (A i) <
        min (StrategicAlloc.RRFair.val v i E) (StrategicAlloc.RRFair.val v i (A i) + v i g) :=
      lt_min hcon (by linarith)
    linarith
