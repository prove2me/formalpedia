-- Prove2me | solution 1 for PersistClust.Count.off_diagonal_fiber_encard
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T11:05:30.569547+00:00
-- url     : https://prove2.me/submissions/bc15e002-b87b-4618-a4d0-35f1265c34b6

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- The off-diagonal copies at a single point: the fiber of `offD D` over `p` has
exactly `D p` slots — one per index below the point's multiplicity. The prom-fiber
half of the §8.16.10 census (an injective routing into this fiber is bounded by
`D p` via `Set.encard_image_le`) reduces to this combinatorial count. -/
theorem solution {D : EReal × EReal → ℕ∞} (p : EReal × EReal) :
    ({q : offD D | offPt q = p}).encard = D p := by
  classical
  by_cases htop : D p = ⊤
  · -- the top case: every `k : ℕ` yields a distinct fiber element; the fiber is infinite
    have hkltop : ∀ k : ℕ, ((k : ℕ∞) < D p) := by
      intro k
      rw [htop]
      exact lt_of_le_of_ne le_top (ENat.natCast_ne_top k)
    have hinj : Function.Injective (fun k : ℕ => ((⟨(p, k), hkltop k⟩ : offD D))) := by
      intro k₁ k₂ h
      have h' : (p, k₁) = (p, k₂) := congrArg Subtype.val h
      exact congrArg Prod.snd h'
    have hinf : ({q : offD D | offPt q = p}).Infinite := by
      have himg : ((fun k : ℕ => ((⟨(p, k), hkltop k⟩ : offD D))) '' Set.univ).Infinite :=
        Set.Infinite.image (fun k₁ _ k₂ _ h => hinj h) (Set.infinite_univ)
      refine Set.Infinite.mono ?_ himg
      intro q hq
      simp only [Set.mem_image, Set.mem_univ, true_and] at hq
      obtain ⟨k, rfl⟩ := hq
      rfl
    rw [htop]
    exact Set.Infinite.encard_eq hinf
  · -- the finite case: the fiber is in bijection with `Fin (D p).toNat`
    have hco : ((D p).toNat : ℕ∞) = D p := ENat.natCast_toNat htop
    have hidx : ∀ q : ↥({q : offD D | offPt q = p} : Set (offD D)),
        q.val.1.2 < (D p).toNat := by
      intro q
      have hp : q.val.1.1 = p := q.property
      have h1 : ((q.val.1.2 : ℕ) : ℕ∞) < D q.val.1.1 := q.val.2
      rw [hp] at h1
      rw [← hco] at h1
      exact ENat.natCast_lt_natCast.mp h1
    have hemb : Function.Injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) := by
      intro q₁ q₂ h
      have hv : q₁.val.1.2 = q₂.val.1.2 := congrArg Fin.val h
      have hp₁ : (q₁.val.val).1 = p := q₁.property
      have hp₂ : (q₂.val.val).1 = p := q₂.property
      exact Subtype.ext (Subtype.ext (Prod.ext (by rw [hp₁, hp₂]) hv))
    have hfin : ({q : offD D | offPt q = p}).Finite :=
      Set.finite_coe_iff.mpr (Finite.of_injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) hemb)
    haveI : Fintype ↥({q : offD D | offPt q = p} : Set (offD D)) := hfin.fintype
    have hle1 : Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D))
        ≤ (D p).toNat := by
      have h7 := Fintype.card_le_of_injective
        (fun q : ↥({q : offD D | offPt q = p} : Set (offD D)) =>
          (⟨q.val.1.2, hidx q⟩ : Fin ((D p).toNat))) hemb
      rwa [Fintype.card_fin] at h7
    have hbk : ∀ k : Fin ((D p).toNat), ((k : ℕ) : ℕ∞) < D p := by
      intro k
      have h1 : ((k : ℕ) : ℕ∞) < ((D p).toNat : ℕ∞) := ENat.natCast_lt_natCast.mpr k.isLt
      rw [hco] at h1
      exact h1
    have hemb2 : Function.Injective
        (fun k : Fin ((D p).toNat) =>
          (⟨(⟨(p, (k : ℕ)), hbk k⟩ : offD D), rfl⟩ :
            ↥({q : offD D | offPt q = p} : Set (offD D)))) := by
      intro k₁ k₂ h
      have h1 := congrArg Subtype.val h
      have h2 := congrArg Subtype.val h1
      have h3 : (p, (k₁ : ℕ)) = (p, (k₂ : ℕ)) := h2
      injection h3 with _ hk
      exact Fin.val_injective hk
    have hle2 : (D p).toNat
        ≤ Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D)) := by
      have h7 := Fintype.card_le_of_injective
        (fun k : Fin ((D p).toNat) =>
          (⟨(⟨(p, (k : ℕ)), hbk k⟩ : offD D), rfl⟩ :
            ↥({q : offD D | offPt q = p} : Set (offD D)))) hemb2
      rwa [Fintype.card_fin] at h7
    have hcard : Fintype.card ↥({q : offD D | offPt q = p} : Set (offD D))
        = (D p).toNat := le_antisymm hle1 hle2
    rw [← Set.coe_fintypeCard, hcard]
    exact hco
