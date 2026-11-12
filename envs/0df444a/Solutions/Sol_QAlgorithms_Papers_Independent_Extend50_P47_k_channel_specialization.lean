-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P47.k_channel_specialization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:44:36.766626+00:00
-- url     : https://prove2.me/submissions/5cf990dd-8d78-4a87-9cc3-ea4e97d9f8ea

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2BorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2BorelSpace

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Extend50 QAlgorithms.Papers.Independent.Extend50.P47 in
theorem solution [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (n : ℕ) (N : Superop (A × B) (C × D))
    : KChannel n N ↔
    SEChannel (kFamily (A := A) (B := B) n) (kFamily (A := C) (B := D) n) N := by
  constructor
  · rintro ⟨hN, M, hM, ht, hc⟩
    exact ⟨hN, M, ⟨hM, ht⟩, hc⟩
  · rintro ⟨hN, M, ⟨hM, ht⟩, hc⟩
    exact ⟨hN, M, hM, ht, hc⟩
