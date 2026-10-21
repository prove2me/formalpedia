-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.admissible_iff_uAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:12:19.321278+00:00
-- url     : https://prove2.me/submissions/126ab7c2-1466-4108-851f-3fe8dc47020d

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Support21.P14

theorem solution {S : Type*} [CommRing S] [IsDomain S]
    {r : ℕ} (P : GroundParameters S r) :
    UAdmissible P ↔ BMWAdmissible P ∧ Function.Injective (fun j => (P.u j : S)) ∧
      (∀ i j, (P.u i : S) * ↑(P.u j) ≠ 1) := by
  constructor
  · rintro ⟨hq, hu, hp, hw, hl⟩
    refine ⟨⟨hq, fun x hx => ?_, hw, hl⟩, hu, hp⟩
    exact (mul_eq_zero.mp hx).resolve_left hq
  · rintro ⟨⟨hq, -, hw, hl⟩, hu, hp⟩
    exact ⟨hq, hu, hp, hw, hl⟩
