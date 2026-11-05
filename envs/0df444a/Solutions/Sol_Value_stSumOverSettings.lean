-- Prove2me | solution 1 for Value.stSumOverSettings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:46:23.421319+00:00
-- url     : https://prove2.me/submissions/ac43abfe-bc69-4f13-b873-5ab4a40149de

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
theorem _root_.solution : StSumOverSettings := fun _ _ _ => rfl
end Value
