-- Prove2me | solution 1 for arithFriezePatSetNonEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:18:20.534737+00:00
-- url     : https://prove2.me/submissions/4622b6b1-d4a1-4f38-9795-c37bc8fb2997

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Definitions.Def_FriezePatterns_chapter3

set_option autoImplicit true

theorem _root_.solution {n : ℕ} (h : n ≠ 0) : (arithFriezePatSet n).Nonempty  := by
  rcases csteFlute n with ⟨a⟩
  exact ⟨frieze_f a, fluteToFrieze a h⟩
