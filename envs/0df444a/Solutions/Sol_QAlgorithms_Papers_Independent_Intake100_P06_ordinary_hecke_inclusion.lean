-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P06.ordinary_hecke_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:30:40.549276+00:00
-- url     : https://prove2.me/submissions/8c730371-045f-4103-832d-ba39958d0589

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06
noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14


/-- forward letters -/
def AuxOH_L (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) :
    HeckeLetter n false → NormalizedBraidHecke S q n true
  | .g i b => heckeG S q n true i.val b
  | .x i _ => absurd i.2 (by simp)

/-- backward letters -/
def AuxOH_M (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) :
    HeckeLetter n true → NormalizedBraidHecke S q n false
  | .g i b => heckeG S q n false i.val b
  | .x _ _ => 1

theorem AuxOH_LG (S : Type*) [CommRing S] (q : Sˣ) (n i : ℕ) (b : Bool) :
    FreeAlgebra.lift S (AuxOH_L S q n) (heckeFreeG S n false i b) =
      heckeMap S q n true (heckeFreeG S n true i b) := by
  unfold heckeFreeG; split_ifs <;> simp [AuxOH_L, heckeG, heckeFreeG, *]

theorem AuxOH_MG (S : Type*) [CommRing S] (q : Sˣ) (n i : ℕ) (b : Bool) :
    FreeAlgebra.lift S (AuxOH_M S q n) (heckeFreeG S n true i b) =
      heckeMap S q n false (heckeFreeG S n false i b) := by
  unfold heckeFreeG; split_ifs <;> simp [AuxOH_M, heckeG, heckeFreeG, *]

theorem AuxOH_MX (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) (hn : 1 ≤ n) (b : Bool) :
    FreeAlgebra.lift S (AuxOH_M S q n) (heckeFreeX S n true b) = 1 := by
  unfold heckeFreeX; rw [dif_pos (by simp; omega)]; simp [AuxOH_M]

/-- forward -/
def AuxOH_f (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) :
    NormalizedBraidHecke S q n false →ₐ[S] NormalizedBraidHecke S q n true :=
  RingQuot.liftAlgHom S ⟨FreeAlgebra.lift S (AuxOH_L S q n), fun a b h => by
    have mk := fun {a b} (h : NormalizedBraidHeckeRel q n true a b) => RingQuot.mkAlgHom_rel S h
    cases h with
    | inverseL i hi => simpa [AuxOH_LG, heckeMap] using mk (NormalizedBraidHeckeRel.inverseL i hi)
    | inverseR i hi => simpa [AuxOH_LG, heckeMap] using mk (NormalizedBraidHeckeRel.inverseR i hi)
    | braid i hi => simpa [AuxOH_LG, heckeMap] using mk (NormalizedBraidHeckeRel.braid i hi)
    | far i j hi hj hd => simpa [AuxOH_LG, heckeMap] using mk (NormalizedBraidHeckeRel.far i j hi hj hd)
    | xInverseL ha => cases ha
    | xInverseR ha => cases ha
    | typeB ha => cases ha
    | xFar ha => cases ha
    | skein i hi => simpa [AuxOH_LG, heckeMap] using mk (NormalizedBraidHeckeRel.skein i hi)⟩

/-- backward -/
def AuxOH_r (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) :
    NormalizedBraidHecke S q n true →ₐ[S] NormalizedBraidHecke S q n false :=
  RingQuot.liftAlgHom S ⟨FreeAlgebra.lift S (AuxOH_M S q n), fun a b h => by
    have mk := fun {a b} (h : NormalizedBraidHeckeRel q n false a b) => RingQuot.mkAlgHom_rel S h
    cases h with
    | inverseL i hi => simpa [AuxOH_MG, heckeMap] using mk (NormalizedBraidHeckeRel.inverseL i hi)
    | inverseR i hi => simpa [AuxOH_MG, heckeMap] using mk (NormalizedBraidHeckeRel.inverseR i hi)
    | braid i hi => simpa [AuxOH_MG, heckeMap] using mk (NormalizedBraidHeckeRel.braid i hi)
    | far i j hi hj hd => simpa [AuxOH_MG, heckeMap] using mk (NormalizedBraidHeckeRel.far i j hi hj hd)
    | xInverseL ha hn => simp [AuxOH_MX S q n hn]
    | xInverseR ha hn => simp [AuxOH_MX S q n hn]
    | typeB ha hn => simp [AuxOH_MX S q n (by omega), mul_assoc]
    | xFar ha i hi hpos => simp [AuxOH_MX S q n (by omega)]
    | skein i hi => simpa [AuxOH_MG, heckeMap] using mk (NormalizedBraidHeckeRel.skein i hi)⟩

theorem _root_.solution (S : Type*) [CommRing S] (q : Sˣ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : NormalizedBraidHecke S q n false →ₐ[S] NormalizedBraidHecke S q n true,
      Function.Injective f ∧
      ∀ i : ℕ, i + 1 < n → ∀ inverse : Bool,
        f (heckeG S q n false i inverse) = heckeG S q n true i inverse := by
  have hfG : ∀ i b, AuxOH_f S q n (heckeG S q n false i b) = heckeG S q n true i b := by
    intro i b
    simp [AuxOH_f, heckeG, heckeMap, RingQuot.liftAlgHom_mkAlgHom_apply, AuxOH_LG]
  have hrf : (AuxOH_r S q n).comp (AuxOH_f S q n) = AlgHom.id S _ := by
    apply RingQuot.ringQuot_ext'
    refine FreeAlgebra.hom_ext (funext fun l => ?_)
    change AuxOH_r S q n (AuxOH_f S q n (RingQuot.mkAlgHom S _ (FreeAlgebra.ι S l))) =
      RingQuot.mkAlgHom S _ (FreeAlgebra.ι S l)
    rcases l with ⟨⟨i, hi⟩, b⟩ | ⟨⟨i, hi⟩, b⟩
    · simp [AuxOH_f, AuxOH_r, AuxOH_L, RingQuot.liftAlgHom_mkAlgHom_apply, heckeG, heckeMap,
        AuxOH_MG, heckeFreeG, hi]
      simp [AuxOH_M, heckeG, heckeMap, heckeFreeG, hi]
    · simp at hi
  refine ⟨AuxOH_f S q n, ?_, fun i _ b => hfG i b⟩
  intro a b hab
  have := congrArg (AuxOH_r S q n) hab
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hrf] at this

end QAlgorithms.Papers.Independent.Intake100.P06

end
