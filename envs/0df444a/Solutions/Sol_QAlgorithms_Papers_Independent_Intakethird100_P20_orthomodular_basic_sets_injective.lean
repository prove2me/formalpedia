-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.orthomodular_basic_sets_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:04:56.513706+00:00
-- url     : https://prove2.me/submissions/e15dabf5-14a9-47cf-8c24-2cf264b5bd4f

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.1; de Groote, Observables I, PDF p./pp. 43.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) {a b : L} :
    stoneBasic a = stoneBasic b → a = b := by
  classical
  have hp := horth.1
  have hanti {x y : L} (h : x ≤ y) : perp y ≤ perp x := by
    have hh := (hp.2.1 x y).1
    rw [inf_eq_left.mpr h] at hh
    exact sup_le_iff.mp (le_of_eq hh.symm) |>.2
  have hsplit (x d : L) (hd : d ≤ x) : d ⊔ (x ⊓ perp d) = x := by
    have hpd : perp x ≤ perp d := hanti hd
    have hh := horth.2 (perp d) (perp x) d hpd (by rw [hp.2.2 d])
    rw [inf_eq_right.mpr hpd, inf_comm (perp d) d, (hp.1 d).1, sup_bot_eq] at hh
    have hc := congrArg perp hh
    rw [(hp.2.1 (perp d) (perp x ⊔ d)).1,
      (hp.2.1 (perp x) d).2, hp.2.2 d, hp.2.2 x] at hc
    exact hc
  have horder (x y : L) (hsub : stoneBasic x ⊆ stoneBasic y) : x ≤ y := by
    by_contra hxy
    let d := x ⊓ y
    let c := x ⊓ perp d
    have hc : c ≠ ⊥ := by
      intro hz
      have hs := hsplit x d inf_le_left
      change d ⊔ c = x at hs
      rw [hz, sup_bot_eq] at hs
      exact hxy (hs ▸ (inf_le_right : d ≤ y))
    have hbase : IsFilterBase ({c} : Set L) := by
      refine ⟨⟨c, rfl⟩, ?_, ?_⟩
      · intro hz
        exact hc (show c = ⊥ from (Set.mem_singleton_iff.mp hz).symm)
      · intro z hz w hw
        have hzc : z = c := hz
        have hwc : w = c := hw
        subst z
        subst w
        exact ⟨c, rfl, le_rfl, le_rfl⟩
    obtain ⟨D, hD, hsubD⟩ := filter_base_extends_to_quasipoint {c} hbase
    have hcin : c ∈ D := hsubD (Set.mem_singleton c)
    have hu := quasipoint_upward_and_meet_closed D hD
    have hx : x ∈ D := hu.1 c hcin x inf_le_left
    have hy : y ∈ D := hsub (show (⟨D, hD⟩ : StoneSpectrum L) ∈ stoneBasic x from hx)
    have hd : d ∈ D := hu.2 x hx y hy
    have hz := hu.2 d hd c hcin
    have hzero : d ⊓ c = ⊥ := by
      apply le_antisymm _ bot_le
      exact (inf_le_inf_left d (show c ≤ perp d from inf_le_right)).trans_eq (hp.1 d).1
    exact hD.1.2.1 (hzero ▸ hz)
  intro hab
  exact le_antisymm (horder a b hab.subset) (horder b a hab.symm.subset)
