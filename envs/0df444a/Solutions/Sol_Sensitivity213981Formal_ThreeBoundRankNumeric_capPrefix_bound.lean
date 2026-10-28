-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:30:48.980767+00:00
-- url     : https://prove2.me/submissions/ffd32657-0947-43eb-aba0-322d31617441

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Exact q3 prefix caps and converted-arc refinements. The record fields
are counts of actual high heads, incoming hits, and residual prefixes. -/


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric
open scoped BigOperators












theorem tighten_bound (a base cap : ℕ) (p : Prop) [Decidable p]
    (hb : a ≤  base) (hc : p → a ≤  cap) : a ≤  tighten base cap p := by
  unfold tighten
  split_ifs with hh
  · exact le_min hb (hc hh)
  · exact hb













theorem capPrefix_bound (caps : Caps) (r : Record) (q a : ℕ) (hq : q ≤  3)
    (hbase : a ≤  min (Caps.at caps.ordinary q-1-lowCount r q)
      (Caps.at caps.ordinary q-nextCount r q))
    (hs : q=0 → 1 ≤  headCount r → a ≤  positivePrefix r q+caps.pcross+r 34)
    (hd : q=0 → 2 ≤  headCount r → a ≤  positivePrefix r q+Caps.at caps.zero 2+r 35)
    (hm₁ : q≠0 → 1 ≤  eligibleCount r q →
      a ≤  Caps.at caps.marked (q-1)-1+(1-nextCount r q))
    (hm₂ : q≠0 → q ≤  2 → 2 ≤  eligibleCount r q →
      a ≤  Caps.at caps.marked (if q=1 then 4 else 5)-1+(2-nextCount r q))
    (hz₁ : q=1 → 3 ≤  headCount r → a ≤  positivePrefix r q+(Caps.at caps.marked 6-1)+r 36)
    (hz₂ : q=2 → 4 ≤  headCount r → a ≤  positivePrefix r q+(Caps.at caps.marked 7-1)+r 37)
    (hz₃ : q=3 → 5 ≤  headCount r → a ≤  positivePrefix r q+(Caps.at caps.marked 8-1)+r 38)
    (hz₄ : q=3 → 6 ≤  headCount r → a ≤  positivePrefix r q+(Caps.at caps.marked 9-1)+r 39)
    (hz₅ : q=3 → 7 ≤  headCount r → a ≤  positivePrefix r q+(Caps.at caps.marked 11-1)+r 40) :
    a ≤  capPrefix caps r q := by
  unfold capPrefix
  apply tighten_bound
  ·
    apply tighten_bound
    ·
      apply tighten_bound
      ·
        apply tighten_bound
        ·
          apply tighten_bound
          ·
            apply tighten_bound
            ·
              apply tighten_bound
              ·
                apply tighten_bound
                ·
                  apply tighten_bound
                  ·
                    exact hbase
                  · rintro ⟨hq0,hh⟩; exact hs hq0 hh
                · rintro ⟨hq0,hh⟩; exact hd hq0 hh
              · rintro ⟨hq0,hh⟩; exact hm₁ hq0 hh
            · rintro ⟨hq0,hq2,hh⟩; exact hm₂ hq0 hq2 hh
          · rintro ⟨he,hh⟩; exact hz₁ he hh
        · rintro ⟨he,hh⟩; exact hz₂ he hh
      · rintro ⟨he,hh⟩; exact hz₃ he hh
    · rintro ⟨he,hh⟩; exact hz₄ he hh
  · rintro ⟨he,hh⟩; exact hz₅ he hh



end ThreeBoundRankNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record)
  (q a : Nat) (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hbase :
    @LE.le.{0} Nat instLENat a
      (@Min.min.{0} Nat instMinNat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.ordinary caps) q)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.lowCount r q))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.ordinary caps) q)
          (Sensitivity213981Formal.ThreeBoundRankNumeric.nextCount r q))))
  (hs :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.pcross caps))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))))
  (hd :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.zero caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35))))))
  (hm₁ :
    @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.eligibleCount r q) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) q
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (Sensitivity213981Formal.ThreeBoundRankNumeric.nextCount r q))))
  (hm₂ :
    @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.eligibleCount r q) →
          @LE.le.{0} Nat instLENat a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@ite.{1} Nat (@Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (instDecidableEqNat q (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (Sensitivity213981Formal.ThreeBoundRankNumeric.nextCount r q))))
  (hz₁ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))))
  (hz₂ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 37) (instOfNatNat (nat_lit 37))))))
  (hz₃ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))))
  (hz₄ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))))))
  (hz₅ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.headCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                  (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                  (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (r (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))))),
  @LE.le.{0} Nat instLENat a (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q) := @Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix_bound
