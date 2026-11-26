-- Prove2me | solution 1 for RobersonCx.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-26T16:38:43.583861+00:00
-- url     : https://prove2.me/submissions/81a3e73a-e549-416e-8100-78947a82d1ab

import Mathlib.GroupTheory.Perm.Cycle.Type
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_QuotIsoTo

set_option autoImplicit false

open RobersonCx

private def precompose {V X : Type} {F : SimpleGraph V} {GX : SimpleGraph X}
    (σ : F ≃g F) : Function.End (F →g GX) :=
  fun f => f.comp σ.toHom

private theorem precompose_pow_apply {V X : Type} {F : SimpleGraph V} {GX : SimpleGraph X}
    (σ : F ≃g F) (n : ℕ) (f : F →g GX) (v : V) :
    ((precompose (GX := GX) σ ^ n) f) v = f ((σ ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ]
    change ((precompose (GX := GX) σ ^ n) f) (σ v) = f ((σ ^ n) (σ v))
    exact ih (σ v)

private theorem fixed_on_orbits {V X : Type} {F : SimpleGraph V} {GX : SimpleGraph X}
    (σ : F ≃g F) (f : F →g GX) (hf : precompose σ f = f) {a b : V}
    (hab : MulAction.orbitRel (Subgroup.zpowers σ.toEquiv) V a b) : f a = f b := by
  let preserving : Subgroup (Equiv.Perm V) :=
    { carrier := {g | ∀ v, f (g v) = f v}
      one_mem' := fun _ => rfl
      mul_mem' := by
        intro g h hg hh v
        exact (hg (h v)).trans (hh v)
      inv_mem' := by
        intro g hg v
        simpa using (hg (g.symm v)).symm }
  have hgenerator : σ.toEquiv ∈ preserving := fun v => DFunLike.congr_fun hf v
  have hsub : Subgroup.zpowers σ.toEquiv ≤ preserving :=
    Subgroup.zpowers_le.mpr hgenerator
  obtain ⟨g, rfl⟩ := hab
  exact hsub g.property b

private abbrev QuotientMaps {V X : Type} (F : SimpleGraph V) (τ : Equiv.Perm V)
    (GX : SimpleGraph X) :=
  {φ : OrbitQuot τ → X // ∀ O O', quotRel F τ O O' → GX.Adj (φ O) (φ O')}

private def fixedEquivQuotientMaps {V X : Type} {F : SimpleGraph V} {GX : SimpleGraph X}
    (σ : F ≃g F) :
    (Function.fixedPoints (precompose (GX := GX) σ)) ≃
      QuotientMaps F σ.toEquiv GX := by
  let descend (f : Function.fixedPoints (precompose (GX := GX) σ)) :
      QuotientMaps F σ.toEquiv GX := by
    let φ : OrbitQuot σ.toEquiv → X :=
      Quotient.lift (fun v => f.val v) (fun _ _ h => fixed_on_orbits σ f.val f.property h)
    refine ⟨φ, ?_⟩
    rintro _ _ ⟨u, v, rfl, rfl, hadj⟩
    exact f.val.map_adj hadj
  let pullback (φ : QuotientMaps F σ.toEquiv GX) :
      Function.fixedPoints (precompose (GX := GX) σ) := by
    let f : F →g GX :=
      ⟨fun v => φ.val (Quotient.mk _ v), fun {u v} hadj =>
        φ.property _ _ ⟨u, v, rfl, rfl, hadj⟩⟩
    refine ⟨f, ?_⟩
    change precompose σ f = f
    apply DFunLike.ext
    intro v
    change φ.val (Quotient.mk _ (σ v)) = φ.val (Quotient.mk _ v)
    apply congrArg φ.val
    apply Quotient.sound
    exact ⟨⟨σ.toEquiv, ⟨1, zpow_one σ.toEquiv⟩⟩, rfl⟩
  refine ⟨descend, pullback, ?_, ?_⟩
  · intro f
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    rfl
  · intro φ
    apply Subtype.ext
    funext O
    exact Quotient.inductionOn O (fun _ => rfl)

theorem solution {V : Type} [Finite V] (F : SimpleGraph V) (p : ℕ) (hp : p.Prime) (σ : F ≃g F)
    (hσ : orderOf σ = p) (X : Type) [Finite X] (GX : SimpleGraph X) :
    homCount F GX ≡ homCountQuot F σ.toEquiv GX [MOD p] := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fintype (F →g GX) := Fintype.ofFinite _
  have hpow : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hperiod : precompose (GX := GX) σ ^ (p ^ 1) = 1 := by
    rw [pow_one]
    funext f
    apply DFunLike.ext
    intro v
    rw [precompose_pow_apply, hpow]
    rfl
  change Nat.card (F →g GX) ≡ Nat.card (QuotientMaps F σ.toEquiv GX) [MOD p]
  rw [← Nat.card_congr (fixedEquivQuotientMaps (GX := GX) σ)]
  simpa only [← Nat.card_eq_fintype_card] using
    (Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hperiod)
