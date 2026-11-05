-- Prove2me | solution 1 for Value.stCopiesMustAgree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:43:26.956551+00:00
-- url     : https://prove2.me/submissions/38149139-c3c3-458c-b81d-2f60fcc331bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique

set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
namespace Value
theorem _root_.solution : StCopiesMustAgree := by
  intro K lam W z
  constructor
  · intro h
    obtain ⟨p, hp⟩ := not_forall.1 h
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    unfold cliqueTerm
    rw [Finset.prod_eq_zero hp (if_neg hne), mul_zero]
  · intro h
    unfold cliqueTerm
    rw [Finset.prod_eq_one fun p hp => if_pos (h p hp), mul_one]
end Value
