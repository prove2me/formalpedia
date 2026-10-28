-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:31:59.64802+00:00
-- url     : https://prove2.me/submissions/f01ded10-483e-4322-9379-08a8317552e8

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















theorem convertedCap_bound (caps : Caps) (perfect : ℕ) (r : Record) (e q a : ℕ) (hq : q ≤  3)
    (hbase : a ≤  capPrefix caps r q-positivePrefix r q)
    (hs : q=0 → 1 ≤  guardCount r → a ≤  caps.pcross+allowance 1 e (guardCount r))
    (hd : q=0 → 2 ≤  guardCount r → a ≤  Caps.at caps.zero 2+allowance 2 e (guardCount r))
    (ht : q=0 → 3 ≤  guardCount r → a ≤  perfect+allowance 3 e (guardCount r))
    (hz₁ : q=1 → 3 ≤  guardCount r → a ≤  Caps.at caps.marked 6-1+allowance 3 e (guardCount r))
    (hz₂ : q=2 → 4 ≤  guardCount r → a ≤  Caps.at caps.marked 7-1+allowance 4 e (guardCount r))
    (hz₃ : q=3 → 5 ≤  guardCount r → a ≤  Caps.at caps.marked 8-1+allowance 5 e (guardCount r))
    (hz₄ : q=3 → 6 ≤  guardCount r → a ≤  Caps.at caps.marked 9-1+allowance 6 e (guardCount r))
    (hz₅ : q=3 → 7 ≤  guardCount r → a ≤  Caps.at caps.marked 11-1+allowance 7 e (guardCount r)) :
    a ≤  convertedCap caps perfect r e q := by
  unfold convertedCap
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
                · rintro ⟨he,hh⟩; exact hs he hh
              · rintro ⟨he,hh⟩; exact hd he hh
            · rintro ⟨he,hh⟩; exact ht he hh
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
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (e q a : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hbase :
    @LE.le.{0} Nat instLENat a
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (Sensitivity213981Formal.ThreeBoundRankNumeric.capPrefix caps r q)
        (Sensitivity213981Formal.ThreeBoundRankNumeric.positivePrefix r q)))
  (hs :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.pcross caps)
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hd :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.zero caps)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (ht :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) perfect
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₁ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₂ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₃ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₄ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r))))
  (hz₅ :
    @Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
          (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r) →
        @LE.le.{0} Nat instLENat a
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (Sensitivity213981Formal.ThreeBoundNumeric.Caps.at
                (Sensitivity213981Formal.ThreeBoundNumeric.Caps.marked caps)
                (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) e
              (Sensitivity213981Formal.ThreeBoundRankNumeric.guardCount r)))),
  @LE.le.{0} Nat instLENat a (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r e q) := @Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap_bound
