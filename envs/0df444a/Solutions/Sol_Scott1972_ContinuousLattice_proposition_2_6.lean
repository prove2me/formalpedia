-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:18.141151+00:00
-- url     : https://prove2.me/submissions/fb822e7b-4303-4855-b809-2fd369631c72

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (f : D × D' → D'') :
    PreservesDirectedSup f ↔
      (∀ y, PreservesDirectedSup fun x => f (x, y)) ∧
        (∀ x, PreservesDirectedSup fun y => f (x, y)) := by
  constructor
  · -- joint continuity ⟹ separate continuity (precompose with the continuous slice maps)
    intro hf
    refine ⟨fun y S hS hSdir => ?_, fun x S hS hSdir => ?_⟩
    · set T : Set (D × D') := (fun x => (x, y)) '' S with hT
      have hTne : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
        exact ⟨(c, y), Set.mem_image_of_mem _ hc, ⟨hac, le_rfl⟩, ⟨hbc, le_rfl⟩⟩
      have hfst : Prod.fst '' T = S := by rw [hT, Set.image_image]; simp
      have hsnd : Prod.snd '' T = {y} := by rw [hT, Set.image_image]; exact hS.image_const y
      have hsupT : sSup T = (sSup S, y) := by
        have e1 : (sSup T).1 = sSup S := by rw [Prod.fst_sSup, hfst]
        have e2 : (sSup T).2 = y := by rw [Prod.snd_sSup, hsnd, sSup_singleton]
        exact Prod.ext_iff.mpr ⟨e1, e2⟩
      have h := hf hTne hTdir
      rw [hsupT, hT, Set.image_image] at h
      simpa using h
    · set T : Set (D × D') := (fun y => (x, y)) '' S with hT
      have hTne : T.Nonempty := hS.image _
      have hTdir : DirectedOn (· ≤ ·) T := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
        exact ⟨(x, c), Set.mem_image_of_mem _ hc, ⟨le_rfl, hac⟩, ⟨le_rfl, hbc⟩⟩
      have hfst : Prod.fst '' T = {x} := by rw [hT, Set.image_image]; exact hS.image_const x
      have hsnd : Prod.snd '' T = S := by rw [hT, Set.image_image]; simp
      have hsupT : sSup T = (x, sSup S) := by
        have e1 : (sSup T).1 = x := by rw [Prod.fst_sSup, hfst, sSup_singleton]
        have e2 : (sSup T).2 = sSup S := by rw [Prod.snd_sSup, hsnd]
        exact Prod.ext_iff.mpr ⟨e1, e2⟩
      have h := hf hTne hTdir
      rw [hsupT, hT, Set.image_image] at h
      simpa using h
  · -- separate continuity ⟹ joint continuity (Scott 1972's directedness argument)
    rintro ⟨h1, h2⟩ Sstar hne hdir
    have hmono1 : ∀ y, Monotone fun x => f (x, y) := fun y => preservesDirectedSup_monotone (h1 y)
    have hmono2 : ∀ x, Monotone fun y => f (x, y) := fun x => preservesDirectedSup_monotone (h2 x)
    have hmono : Monotone f := by
      rintro ⟨a, b⟩ ⟨c, d⟩ hpq
      exact le_trans (hmono1 b hpq.1) (hmono2 c hpq.2)
    have hSne : (Prod.fst '' Sstar).Nonempty := hne.image _
    have hS'ne : (Prod.snd '' Sstar).Nonempty := hne.image _
    have hSdir : DirectedOn (· ≤ ·) (Prod.fst '' Sstar) := hdir.fst
    have hS'dir : DirectedOn (· ≤ ·) (Prod.snd '' Sstar) := hdir.snd
    have hsupStar : sSup Sstar = (sSup (Prod.fst '' Sstar), sSup (Prod.snd '' Sstar)) :=
      Prod.ext_iff.mpr ⟨Prod.fst_sSup _, Prod.snd_sSup _⟩
    apply le_antisymm
    · rw [hsupStar]
      have e1 : f (sSup (Prod.fst '' Sstar), sSup (Prod.snd '' Sstar))
          = sSup ((fun x => f (x, sSup (Prod.snd '' Sstar))) '' (Prod.fst '' Sstar)) :=
        h1 (sSup (Prod.snd '' Sstar)) hSne hSdir
      rw [e1]
      apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      show f (x, sSup (Prod.snd '' Sstar)) ≤ sSup (f '' Sstar)
      have e2 : f (x, sSup (Prod.snd '' Sstar))
          = sSup ((fun y => f (x, y)) '' (Prod.snd '' Sstar)) :=
        h2 x hS'ne hS'dir
      rw [e2]
      apply sSup_le
      rintro _ ⟨y, hy, rfl⟩
      show f (x, y) ≤ sSup (f '' Sstar)
      obtain ⟨p, hpS, hpfst⟩ := hx
      obtain ⟨q, hqS, hqsnd⟩ := hy
      obtain ⟨r, hrS, hpr, hqr⟩ := hdir p hpS q hqS
      have hxr : x ≤ r.1 := hpfst ▸ hpr.1
      have hyr : y ≤ r.2 := hqsnd ▸ hqr.2
      calc f (x, y) ≤ f (r.1, r.2) := hmono ⟨hxr, hyr⟩
        _ = f r := by rw [Prod.mk.eta]
        _ ≤ sSup (f '' Sstar) := le_sSup (Set.mem_image_of_mem f hrS)
    · apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      exact hmono (le_sSup hp)
end Scott1972.ContinuousLattice
