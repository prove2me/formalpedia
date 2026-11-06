-- Prove2me | solution 1 for Printed.achievable_of_eStar_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:18:05.248884+00:00
-- url     : https://prove2.me/submissions/f6bc10ab-8c51-4849-b2bb-97241a58edc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
import Theorems.Thm_Printed_stMono
import Theorems.Thm_Printed_half_mem
import Theorems.Thm_QueryMachines_stMono


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by
  obtain ⟨e', he', hlt⟩ := exists_lt_of_csInf_lt ⟨1 / 2, half_mem⟩ he
  obtain ⟨K, hK, hA⟩ := he' K₀
  exact ⟨K, hK, stMono K e' e hA hlt.le⟩
end Printed
