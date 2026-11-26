-- Prove2me | solution 1 for P2M_FixedNumerator_norm_nonneg__64b3937061ea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:36:26.52238+00:00
-- url     : https://prove2.me/submissions/230520b6-8502-473e-b76a-b51c995892f9

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (c : GaussianInt) : 0 ≤ c.norm := Zsqrtd.norm_nonneg (by norm_num) c
end FixedNumerator
