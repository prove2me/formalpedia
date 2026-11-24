-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.map_inj_of_le_ge
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:15:33.425001+00:00
-- url     : https://prove2.me/submissions/e6f8b7c3-1b11-4e0a-9c75-3bca19d46a86

import Mathlib
open AlgebraicGeometry CategoryTheory


theorem solution {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  have he := le_antisymm h1 h2; subst W; simpa using h
