-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P58.normalized_hecke_quotient
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:27:28.739311+00:00
-- url     : https://prove2.me/submissions/a9bbe618-da78-4461-a848-8e7c02ffb9cf

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

section
open QAlgorithms.Papers.Independent.Gap48.P01

/-- letters to Hecke -/
def AuxNH_L (P : NonsplitParameters R k) : CyclotomicLetter 2 → NormalizedHecke P
  | .x _ false => heckeGen P .t1
  | .x _ true => heckeGen P .t1Inv
  | .e _ => 0
  | .y _ false => heckeGen P .t0
  | .y _ true => heckeGen P .t0Inv

/-- free to Hecke -/
def AuxNH_phi (P : NonsplitParameters R k) : FreeAlgebra R (CyclotomicLetter 2) →ₐ[R] NormalizedHecke P :=
  FreeAlgebra.lift R (AuxNH_L P)

theorem AuxNH_X (P : NonsplitParameters R k) (i : ℕ) (hi : 1 ≤ i ∧ i < 2) (inv : Bool) :
    AuxNH_phi P (nonsplitFreeX R 2 i inv) = if inv then heckeGen P .t1Inv else heckeGen P .t1 := by
  unfold nonsplitFreeX; rw [dif_pos hi]; cases inv <;> simp [AuxNH_phi, AuxNH_L]

theorem AuxNH_E (P : NonsplitParameters R k) (i : ℕ) :
    AuxNH_phi P (nonsplitFreeE R 2 i) = 0 := by
  unfold nonsplitFreeE; split_ifs <;> simp [AuxNH_phi, AuxNH_L]

theorem AuxNH_Y (P : NonsplitParameters R k) (inv : Bool) :
    AuxNH_phi P (nonsplitFreeY R 2 inv) = if inv then heckeGen P .t0Inv else heckeGen P .t0 := by
  unfold nonsplitFreeY; rw [dif_pos (by decide)]; cases inv <;> simp [AuxNH_phi, AuxNH_L]

theorem AuxNH_hrel (P : NonsplitParameters R k) {a b : FreeAlgebra R HeckeLetter}
    (h : NormalizedHeckeRel P a b) :
    RingQuot.mkAlgHom R (NormalizedHeckeRel P) a = RingQuot.mkAlgHom R (NormalizedHeckeRel P) b :=
  RingQuot.mkAlgHom_rel R h

theorem AuxNH_t1inv (P : NonsplitParameters R k) :
    heckeGen P .t1Inv = heckeGen P .t1 - algebraMap R _ (skeinDelta P) := by
  have q := AuxNH_hrel P (NormalizedHeckeRel.quadratic (P := P))
  have r := AuxNH_hrel P (NormalizedHeckeRel.t1Right (P := P))
  simp only [map_pow, map_add, map_mul, map_one, AlgHom.commutes] at q r
  change heckeGen P .t1 ^ 2 = algebraMap R _ (skeinDelta P) * heckeGen P .t1 + 1 at q
  change heckeGen P .t1Inv * heckeGen P .t1 = 1 at r
  set T := heckeGen P .t1
  set a := algebraMap R (NormalizedHecke P) (skeinDelta P)
  have ha : a * T = T * a := Algebra.commutes _ _
  calc heckeGen P .t1Inv = heckeGen P .t1Inv * (T ^ 2 - a * T) := by
        rw [q, add_sub_cancel_left, mul_one]
    _ = (heckeGen P .t1Inv * T) * (T - a) := by rw [ha, pow_two, mul_assoc, mul_sub T]
    _ = T - a := by rw [r, one_mul]

theorem AuxNH_rel (P : NonsplitParameters R k) ⦃a b : FreeAlgebra R (CyclotomicLetter 2)⦄
    (h : NonsplitBMWRel P 2 a b) : AuxNH_phi P a = AuxNH_phi P b := by
  have mk := fun {a b} (h : NormalizedHeckeRel P a b) => AuxNH_hrel P h
  have h1 : (1 ≤ 1 ∧ 1 < 2) := by norm_num
  cases h with
  | invL i hi => simpa [AuxNH_X P i hi, heckeGen] using mk (NormalizedHeckeRel.t1Left)
  | invR i hi => simpa [AuxNH_X P i hi, heckeGen] using mk (NormalizedHeckeRel.t1Right)
  | yInvL hn => simpa [AuxNH_Y, heckeGen] using mk (NormalizedHeckeRel.t0Left)
  | yInvR hn => simpa [AuxNH_Y, heckeGen] using mk (NormalizedHeckeRel.t0Right)
  | skein i hi =>
    simp only [map_sub, map_mul, map_one, AlgHom.commutes, AuxNH_X P i hi, AuxNH_E, sub_zero,
      mul_one, Bool.false_eq_true, if_false, if_true, AuxNH_t1inv]
    abel
  | xFar i j hi hj hd => exfalso; omega
  | braid i hi => exfalso; omega
  | xeFar i j hi hj hd => exfalso; omega
  | eeFar i j hi hj hd => exfalso; omega
  | xe i hi => simp [AuxNH_E]
  | ex i hi => simp [AuxNH_E]
  | nearL i j hi hj hd => exfalso; omega
  | nearR i j hi hj hd => exfalso; omega
  | tripleE i j hi hj hd => exfalso; omega
  | squareE i hi => simp [AuxNH_E]
  | cyclotomic hn =>
    have := mk (NormalizedHeckeRel.cyclotomic)
    simp only [map_pow, map_sum, map_mul, AlgHom.commutes] at this ⊢
    simpa [AuxNH_Y, heckeGen] using this
  | affine hn =>
    have := mk (NormalizedHeckeRel.braid)
    simp only [map_mul] at this ⊢
    simp only [AuxNH_X P 1 h1, AuxNH_Y, Bool.false_eq_true, if_false, heckeGen]
    exact this.symm
  | yx i hi => exfalso; omega
  | ye i hi => exfalso; omega
  | unwrapL hn => simp [AuxNH_E]
  | unwrapR hn => simp [AuxNH_E]
  | loop m hn => simp [AuxNH_E]

/-- B to Hecke -/
def AuxNH_f0 (P : NonsplitParameters R k) : TwoStrandBMW P →ₐ[R] NormalizedHecke P :=
  RingQuot.liftAlgHom R ⟨AuxNH_phi P, fun a b h => AuxNH_rel P h⟩

theorem AuxNH_f0_mk (P : NonsplitParameters R k) (a) :
    AuxNH_f0 P (RingQuot.mkAlgHom R (NonsplitBMWRel P 2) a) = AuxNH_phi P a := by
  simp [AuxNH_f0, RingQuot.liftAlgHom_mkAlgHom_apply]

theorem AuxNH_f0_I (P : NonsplitParameters R k) (z : TwoStrandBMW P) (hz : z ∈ twoSidedIdeal P) :
    AuxNH_f0 P z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi1, hi2, a, b, rfl⟩ := hz
    have : AuxNH_f0 P (E P 2 i) = 0 := by
      rw [E, presentationMap, AuxNH_f0_mk, AuxNH_E]
    rw [map_mul, map_mul, this, mul_zero, zero_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

/-- forward map -/
def AuxNH_f (P : NonsplitParameters R k) : EQuotient P →ₐ[R] NormalizedHecke P :=
  RingQuot.liftAlgHom R ⟨AuxNH_f0 P, fun a b h => by
    have := AuxNH_f0_I P _ h
    rw [map_sub, sub_eq_zero] at this; exact this⟩

theorem AuxNH_f_mk (P : NonsplitParameters R k) (a : TwoStrandBMW P) :
    AuxNH_f P (eQuotientMap P a) = AuxNH_f0 P a := by
  simp [AuxNH_f, eQuotientMap, RingQuot.liftAlgHom_mkAlgHom_apply]

/-- Hecke letters to quotient -/
def AuxNH_G (P : NonsplitParameters R k) : HeckeLetter → EQuotient P
  | .t0 => eQuotientMap P (y P)
  | .t0Inv => eQuotientMap P (yInv P)
  | .t1 => eQuotientMap P (x P)
  | .t1Inv => eQuotientMap P (xInv P)

theorem AuxNH_eq_zero (P : NonsplitParameters R k) : eQuotientMap P (e P) = 0 := by
  rw [← map_zero (eQuotientMap P)]
  apply RingQuot.mkAlgHom_rel
  rw [sub_zero]
  apply Submodule.subset_span
  exact ⟨1, le_rfl, by norm_num, 1, 1, by simp [e]⟩

theorem AuxNH_brel (P : NonsplitParameters R k) {a b : FreeAlgebra R (CyclotomicLetter 2)}
    (h : NonsplitBMWRel P 2 a b) :
    eQuotientMap P (RingQuot.mkAlgHom R _ a) = eQuotientMap P (RingQuot.mkAlgHom R _ b) := by
  rw [RingQuot.mkAlgHom_rel R h]

/-- backward map -/
def AuxNH_g (P : NonsplitParameters R k) : NormalizedHecke P →ₐ[R] EQuotient P :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R (AuxNH_G P), fun a b h => by
    have h1 : (1 ≤ 1 ∧ 1 < 2) := by norm_num
    have hx : ∀ inv, eQuotientMap P (RingQuot.mkAlgHom R _ (nonsplitFreeX R 2 1 inv)) =
        eQuotientMap P (Accepted.X P 2 1 inv) := fun _ => rfl
    cases h with
    | t0Left => simpa [ht, AuxNH_G, y, yInv, Y, presentationMap] using AuxNH_brel P (NonsplitBMWRel.yInvL (P := P) (by norm_num))
    | t0Right => simpa [ht, AuxNH_G, y, yInv, Y, presentationMap] using AuxNH_brel P (NonsplitBMWRel.yInvR (P := P) (by norm_num))
    | t1Left => simpa [ht, AuxNH_G, x, xInv, X, presentationMap] using AuxNH_brel P (NonsplitBMWRel.invL (P := P) 1 h1)
    | t1Right => simpa [ht, AuxNH_G, x, xInv, X, presentationMap] using AuxNH_brel P (NonsplitBMWRel.invR (P := P) 1 h1)
    | braid =>
      have := AuxNH_brel P (NonsplitBMWRel.affine (P := P) le_rfl)
      simp only [map_mul] at this
      simpa [ht, AuxNH_G, x, y, X, Y, presentationMap] using this.symm
    | cyclotomic =>
      have := AuxNH_brel P (NonsplitBMWRel.cyclotomic (P := P) (by norm_num))
      simp only [map_pow, map_sum, map_mul, AlgHom.commutes] at this
      simpa [ht, AuxNH_G, y, Y, presentationMap] using this
    | quadratic =>
      have hs := AuxNH_brel P (NonsplitBMWRel.skein (P := P) 1 h1)
      have hxe := AuxNH_brel P (NonsplitBMWRel.xe (P := P) 1 h1)
      have hinv := AuxNH_brel P (NonsplitBMWRel.invL (P := P) 1 h1)
      have he := AuxNH_eq_zero P
      simp only [map_sub, map_mul, map_one, AlgHom.commutes] at hs hxe hinv
      simp only [e, E, presentationMap] at he
      rw [he] at hs hxe
      simp only [map_pow, map_add, map_mul, map_one, AlgHom.commutes, ht, FreeAlgebra.lift_ι_apply,
        AuxNH_G, x]
      simp only [X, presentationMap] at *
      set Xq := eQuotientMap P (RingQuot.mkAlgHom R _ (nonsplitFreeX R 2 1 false))
      set Xi := eQuotientMap P (RingQuot.mkAlgHom R _ (nonsplitFreeX R 2 1 true))
      set a := algebraMap R (EQuotient P) (skeinDelta P)
      have ha : a * Xq = Xq * a := Algebra.commutes _ _
      have hs' : Xq = Xi + a := by
        have h2 := sub_eq_iff_eq_add.mp hs
        rw [h2, add_comm]; congr 1
        first
          | (erw [sub_zero, mul_one])
          | (convert mul_one a using 2; exact sub_zero _)
          | exact (congrArg (a * ·) (sub_zero (1 : EQuotient P))).trans (mul_one a)
      have hq : Xq ^ 2 = Xq * Xq := pow_two Xq
      rw [hq]
      nth_rewrite 2 [hs']
      rw [mul_add, hinv, ← ha, add_comm]⟩

end

theorem _root_.solution (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    ∃ f : EQuotient P ≃ₐ[R] NormalizedHecke P,
      f (eQuotientMap P (y P)) = heckeGen P .t0 ∧
      f (eQuotientMap P (x P)) = heckeGen P .t1 ∧
      f (eQuotientMap P (e P)) = 0 := by
  have hfy : AuxNH_f P (eQuotientMap P (y P)) = heckeGen P .t0 := by
    rw [AuxNH_f_mk]; show AuxNH_f0 P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxNH_f0_mk, QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeY.eq_def] at *
    simp [AuxNH_phi, AuxNH_L]
  have hfx : AuxNH_f P (eQuotientMap P (x P)) = heckeGen P .t1 := by
    rw [AuxNH_f_mk]; show AuxNH_f0 P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxNH_f0_mk, AuxNH_X P 1 (by norm_num)]; rfl
  have hfxi : AuxNH_f P (eQuotientMap P (xInv P)) = heckeGen P .t1Inv := by
    rw [AuxNH_f_mk]; show AuxNH_f0 P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxNH_f0_mk, AuxNH_X P 1 (by norm_num)]; rfl
  have hfyi : AuxNH_f P (eQuotientMap P (yInv P)) = heckeGen P .t0Inv := by
    rw [AuxNH_f_mk]; show AuxNH_f0 P (RingQuot.mkAlgHom R _ _) = _
    rw [AuxNH_f0_mk, AuxNH_Y P true]; rfl
  have hfg : (AuxNH_f P).comp (AuxNH_g P) = AlgHom.id R _ := by
    apply RingQuot.ringQuot_ext'
    refine FreeAlgebra.hom_ext (funext fun l => ?_)
    change AuxNH_f P (AuxNH_g P (RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l))) =
      RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l)
    simp only [AuxNH_g, RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
    cases l
    · exact hfy
    · exact hfyi
    · exact hfx
    · exact hfxi
  have hgf : (AuxNH_g P).comp (AuxNH_f P) = AlgHom.id R _ := by
    apply RingQuot.ringQuot_ext'
    apply RingQuot.ringQuot_ext'
    refine FreeAlgebra.hom_ext (funext fun l => ?_)
    change AuxNH_g P (AuxNH_f P (eQuotientMap P (RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l)))) =
      eQuotientMap P (RingQuot.mkAlgHom R _ (FreeAlgebra.ι R l))
    rw [AuxNH_f_mk, AuxNH_f0_mk]
    simp only [AuxNH_phi, FreeAlgebra.lift_ι_apply]
    rcases l with ⟨⟨i, hi⟩, inv⟩ | ⟨⟨i, hi⟩⟩ | ⟨⟨i, hi⟩, inv⟩
    · obtain rfl : i = 1 := by omega
      cases inv
      · simp only [AuxNH_L, AuxNH_g, heckeGen, RingQuot.liftAlgHom_mkAlgHom_apply, ht,
          FreeAlgebra.lift_ι_apply, AuxNH_G, x, Accepted.X, QAlgorithms.Papers.Independent.Gap48.P01.X,
          QAlgorithms.Papers.Independent.Gap48.P01.presentationMap,
          QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeX]
        rw [dif_pos (by norm_num)]
      · simp only [AuxNH_L, AuxNH_g, heckeGen, RingQuot.liftAlgHom_mkAlgHom_apply, ht,
          FreeAlgebra.lift_ι_apply, AuxNH_G, xInv, Accepted.X, QAlgorithms.Papers.Independent.Gap48.P01.X,
          QAlgorithms.Papers.Independent.Gap48.P01.presentationMap,
          QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeX]
        rw [dif_pos (by norm_num)]
    · obtain rfl : i = 1 := by omega
      have h0 := AuxNH_eq_zero P
      simp only [e, Accepted.E, QAlgorithms.Papers.Independent.Gap48.P01.E,
        QAlgorithms.Papers.Independent.Gap48.P01.presentationMap,
        QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeE] at h0
      rw [dif_pos (by norm_num)] at h0
      simp only [AuxNH_L, map_zero]
      exact h0.symm
    · obtain rfl : i = 0 := by omega
      cases inv
      · simp only [AuxNH_L, AuxNH_g, heckeGen, RingQuot.liftAlgHom_mkAlgHom_apply, ht,
          FreeAlgebra.lift_ι_apply, AuxNH_G, y, Accepted.Y, QAlgorithms.Papers.Independent.Gap48.P01.Y,
          QAlgorithms.Papers.Independent.Gap48.P01.presentationMap,
          QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeY]
        rw [dif_pos (by decide)]
      · simp only [AuxNH_L, AuxNH_g, heckeGen, RingQuot.liftAlgHom_mkAlgHom_apply, ht,
          FreeAlgebra.lift_ι_apply, AuxNH_G, yInv, Accepted.Y, QAlgorithms.Papers.Independent.Gap48.P01.Y,
          QAlgorithms.Papers.Independent.Gap48.P01.presentationMap,
          QAlgorithms.Papers.Independent.Gap48.P01.nonsplitFreeY]
        rw [dif_pos (by decide)]
  refine ⟨AlgEquiv.ofAlgHom (AuxNH_f P) (AuxNH_g P) hfg hgf, hfy, hfx, ?_⟩
  show AuxNH_f P _ = 0
  rw [AuxNH_eq_zero, map_zero]

end QAlgorithms.Papers.Independent.Intake100.P58

end
