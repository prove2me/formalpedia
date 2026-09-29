-- Prove2me | solution 1 for TarchaBraids.prop_3_17_braid_inclusion_injective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-21T15:20:57.550979+00:00
-- url     : https://prove2.me/submissions/55c6e309-292a-41f4-bf08-e8f6b1e5fd73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Theorems.Thm_TarchaBraids_braid_inclusion_split

set_option autoImplicit false

open TarchaBraids
open BraidsLinksMCG

/-- Prop 3.17: the braid inclusion B_m -> B_n is injective. The split
    inclusion child (still open) provides the hom f and its retraction g;
    injectivity follows because g (f a) = a and g (f b) = b force a = b
    whenever f a = f b. -/
theorem solution {m n : ℕ} (h : m ≤ n) :
    ∃ f : ArtinBraidGroup m →* ArtinBraidGroup n,
      (∀ i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i)) ∧
      Function.Injective f :=
  match braid_inclusion_split h with
  | ⟨f, h1⟩ =>
    match h1 with
    | ⟨hf_spec, h2⟩ =>
      match h2 with
      | ⟨g, hg⟩ =>
        ⟨f, hf_spec, fun a b hab =>
          (hg a).symm.trans ((congrArg (fun y => g y) hab).trans (hg b))⟩
