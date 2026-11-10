-- Prove2me | solution 1 for Pr6453Root.address_data
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-09T09:02:19.292261+00:00
-- url     : https://prove2.me/submissions/04fc7782-125d-4841-8386-6fdbc7eeb927

import Definitions.Def_Pr6453RootAddress

set_option autoImplicit false

theorem solution :
    Fintype.card Pr6453Root.Mask = 16 ∧ Fintype.card Pr6453Root.Address = 192 ∧
      2 * Fintype.card Pr6453Root.Mask * 36 = 1152 :=
  ⟨Pr6453Root.mask_count, Pr6453Root.address_count, Pr6453Root.stage_coefficients⟩
