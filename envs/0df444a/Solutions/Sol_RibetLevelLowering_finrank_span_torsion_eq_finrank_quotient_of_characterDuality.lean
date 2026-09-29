-- Prove2me | solution 1 for RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/35553569-8ca4-5da0-96ed-564a744c0115

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality

set_option Elab.async false

set_option autoImplicit false

namespace RibetLevelLowering

open ModularCurve

private theorem eps_smul_all {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    (Tp : Submodule HeckeAlg J) {L : Type*} [AddCommGroup L] [Module HeckeAlg L]
    {μ : Type*} [AddCommGroup μ] (ε : ↥Tp ≃+ (L →+ μ))
    (hε : ∀ (ℓ : Nat.Primes) (y : ↥Tp) (l : L), ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l))
    (t : HeckeAlg) (y : ↥Tp) (l : L) : ε (t • y) l = ε y (t • l) := by
  let S : Subring HeckeAlg :=
    { carrier := {t | ∀ (y : ↥Tp) (l : L), ε (t • y) l = ε y (t • l)}
      mul_mem' := fun {s t} hs ht y l => by
        show ε ((s * t) • y) l = ε y ((s * t) • l)
        rw [mul_smul, hs, ht, mul_comm s t, mul_smul]
      one_mem' := fun y l => by
        show ε ((1 : HeckeAlg) • y) l = ε y ((1 : HeckeAlg) • l)
        rw [one_smul, one_smul]
      add_mem' := fun {s t} hs ht y l => by
        show ε ((s + t) • y) l = ε y ((s + t) • l)
        rw [add_smul, add_smul, map_add, map_add, AddMonoidHom.add_apply, hs, ht]
      zero_mem' := fun y l => by
        show ε ((0 : HeckeAlg) • y) l = ε y ((0 : HeckeAlg) • l)
        rw [zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
      neg_mem' := fun {s} hs y l => by
        show ε ((-s) • y) l = ε y ((-s) • l)
        have h0 : ε ((-s) • y) l + ε (s • y) l = 0 := by
          rw [← AddMonoidHom.add_apply, ← map_add, ← add_smul, neg_add_cancel, zero_smul, map_zero,
            AddMonoidHom.zero_apply]
        have h1 : ε y ((-s) • l) + ε y (s • l) = 0 := by
          rw [← map_add, ← add_smul, neg_add_cancel, zero_smul, map_zero]
        rw [hs] at h0
        exact (eq_neg_of_add_eq_zero_left h0).trans (eq_neg_of_add_eq_zero_left h1).symm }
  have hle : Algebra.adjoin ℤ (Set.range heckeGen) ≤ subalgebraOfSubring S :=
    Algebra.adjoin_le (by
      rintro _ ⟨ℓ, rfl⟩
      show ∀ (y : ↥Tp) (l : L), ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l)
      exact fun y l => hε ℓ y l)
  have ht : t ∈ (⊤ : Subalgebra ℤ HeckeAlg) := Algebra.mem_top
  rw [← adjoin_range_heckeGen] at ht
  exact mem_subalgebraOfSubring.mp (hle ht) y l

private theorem finrank_eq_of_natCard_eq (K : Type*) [DivisionRing K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Finite V] [Finite W]
    (h : Nat.card V = Nat.card W) : Module.finrank K V = Module.finrank K W := by
  have hV := Module.natCard_eq_pow_finrank (K := K) (V := V)
  have hW := Module.natCard_eq_pow_finrank (K := K) (V := W)
  have key : Nat.card K ^ Module.finrank K V = Nat.card K ^ Module.finrank K W :=
    hV.symm.trans (h.trans hW)
  by_cases h2 : 2 ≤ Nat.card K
  · exact Nat.pow_right_injective h2 key
  · have hc0 : Nat.card K = 0 := by
      have hne1 : Nat.card K ≠ 1 := fun h1 =>
        not_subsingleton K (Nat.card_eq_one_iff_unique.1 h1).1
      omega
    have hzero : ∀ n : ℕ, Nat.card K ^ n ≠ 0 → n = 0 := by
      intro n hn
      by_contra hn0
      exact hn (by rw [hc0, zero_pow hn0])
    have hVne : Nat.card V ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    have hWne : Nat.card W ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
    rw [hV] at hVne
    rw [hW] at hWne
    rw [hzero _ hVne, hzero _ hWne]

set_option backward.isDefEq.respectTransparency false in

private theorem card_hom_eq_card_of_prime_torsion (G μ : Type*) [AddCommGroup G]
    [AddCommGroup μ] [AddGroup.FG G] {p : ℕ} [Module (ZMod p) G] (hp : p.Prime)
    (hG : ∀ g : G, p • g = 0) (hμ : Nat.card μ = p) : Finite G ∧ Finite (G →+ μ) ∧ Nat.card (G →+ μ) = Nat.card G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hμfin : Finite μ := Nat.finite_of_card_ne_zero (by rw [hμ]; exact hp.ne_zero)
  have hpμ : ∀ x : μ, p • x = 0 := fun x => by
    have h := card_nsmul_eq_zero' (G := μ) (x := x)
    rwa [hμ] at h
  letI modμ : Module (ZMod p) μ := AddCommGroup.zmodModule hpμ

  haveI hGmodfin : Module.Finite (ZMod p) G := by
    obtain ⟨S, hS⟩ := AddGroup.fg_def.1 ‹AddGroup.FG G›
    refine ⟨⟨S, ?_⟩⟩
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ AddSubgroup.closure (S : Set G) := by
      rw [hS]; exact AddSubgroup.mem_top v
    exact (AddSubgroup.closure_le ((Submodule.span (ZMod p) (S : Set G)).toAddSubgroup)).2
      (fun x hx => Submodule.subset_span hx) hv
  haveI hGfin : Finite G :=
    AddCommGroup.finite_of_fg_torsion G
      (fun g => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp.pos, hG g⟩)
  let b := Module.finBasis (ZMod p) G

  let e12 : (G →+ μ) ≃ (Fin (Module.finrank (ZMod p) G) → μ) :=
    (AddMonoidHom.toZModLinearMapEquiv p).toEquiv.trans (b.constr (ZMod p)).symm.toEquiv
  haveI hHfin : Finite (G →+ μ) := Finite.of_equiv _ e12.symm
  refine ⟨hGfin, hHfin, ?_⟩
  rw [Nat.card_congr e12, Nat.card_fun, hμ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := G), Nat.card_zmod]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in

private theorem finrank_span_torsion_eq_finrank_quotient_of_characterDuality
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    (𝒯 : Submodule HeckeAlg J) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    {p : ℕ} (hp : p.Prime) (hpm : (p : HeckeAlg) ∈ 𝔪)
    {L : Type*} [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    {μ : Type*} [AddCommGroup μ] (hμ : Nat.card μ = p)
    (ε : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)) ≃+ (L →+ μ))
    (hε : ∀ (ℓ : Nat.Primes) (y : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) (l : L),
      ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l)) :
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J))) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩

  have hall : ∀ (t : HeckeAlg) (y : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)))
      (l : L), ε (t • y) l = ε y (t • l) :=
    eps_smul_all (𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)) ε hε

  have hpW : ∀ w : ↥(heckeTorsion J 𝔪), (p : HeckeAlg) • (w : J) = 0 := fun w =>
    (Submodule.mem_torsionBySet_iff _ _).1 w.2 ⟨(p : HeckeAlg), hpm⟩
  let A : Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion J 𝔪) :=
    { carrier := (Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J)
      add_mem' := fun {x y} hx hy => 𝒯.add_mem hx hy
      zero_mem' := 𝒯.zero_mem
      smul_mem' := by
        intro c x hx
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [Submodule.torsionBySet.mk_smul]
        exact 𝒯.smul_mem t hx }
  have hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J)) = A :=
    Submodule.span_eq A
  rw [hspan]

  have memTp : ∀ w : ↥(heckeTorsion J 𝔪), (w : J) ∈ 𝒯 →
      (w : J) ∈ 𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg) := by
    intro w hw
    refine Submodule.mem_inf.2 ⟨hw, ?_⟩
    rw [Submodule.mem_torsionBy_iff]
    exact hpW w
  let yOf : ↥A → ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)) := fun w =>
    ⟨((w : ↥(heckeTorsion J 𝔪)) : J),
      memTp (w : ↥(heckeTorsion J 𝔪)) (show ((w : ↥(heckeTorsion J 𝔪)) : J) ∈ 𝒯 from w.2)⟩

  have hN_smul : ∀ t ∈ 𝔪, ∀ l : L, t • l ∈ (𝔪 • (⊤ : Submodule HeckeAlg L)) :=
    fun t ht l => Submodule.smul_mem_smul ht Submodule.mem_top

  have hkill : ∀ (w : ↥A) (t : HeckeAlg), t ∈ 𝔪 → ∀ l : L, ε (yOf w) (t • l) = 0 := by
    intro w t ht l
    have htw : t • yOf w = 0 := by
      apply Subtype.ext
      show t • (((w : ↥(heckeTorsion J 𝔪)) : J)) = 0
      exact (Submodule.mem_torsionBySet_iff _ _).1 (w : ↥(heckeTorsion J 𝔪)).2 ⟨t, ht⟩
    rw [← hall, htw, map_zero, AddMonoidHom.zero_apply]
  have hker : ∀ w : ↥A, (𝔪 • (⊤ : Submodule HeckeAlg L)).restrictScalars ℤ ≤
      LinearMap.ker (ε (yOf w)).toIntLinearMap := by
    intro w x hx
    rw [LinearMap.mem_ker]
    show ε (yOf w) x = 0
    have hx' : x ∈ (𝔪 • (⊤ : Submodule HeckeAlg L)) := hx
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro t ht l _
      exact hkill w t ht l
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]

  let gOf : ↥A → ((L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) →+ μ) := fun w =>
    (((𝔪 • (⊤ : Submodule HeckeAlg L)).restrictScalars ℤ).liftQ (ε (yOf w)).toIntLinearMap
        (hker w)).toAddMonoidHom.comp
      (Submodule.Quotient.restrictScalarsEquiv ℤ
        (𝔪 • (⊤ : Submodule HeckeAlg L))).symm.toLinearMap.toAddMonoidHom
  have gOf_mk : ∀ (w : ↥A) (l : L), gOf w (Submodule.Quotient.mk l) = ε (yOf w) l := by
    intro w l
    show (((𝔪 • (⊤ : Submodule HeckeAlg L)).restrictScalars ℤ).liftQ (ε (yOf w)).toIntLinearMap
        (hker w)) ((Submodule.Quotient.restrictScalarsEquiv ℤ
          (𝔪 • (⊤ : Submodule HeckeAlg L))).symm (Submodule.Quotient.mk l)) = ε (yOf w) l
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
    rfl
  let fOf : ((L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) →+ μ) → (L →+ μ) := fun g =>
    g.comp (𝔪 • (⊤ : Submodule HeckeAlg L)).mkQ.toAddMonoidHom
  have hyInv_tors : ∀ g : (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) →+ μ,
      ((ε.symm (fOf g) : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) : J) ∈
        heckeTorsion J 𝔪 := by
    intro g
    show _ ∈ Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg)
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨t, ht⟩
    show t • ((ε.symm (fOf g) : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) : J) = 0
    rw [← Submodule.coe_smul]
    have hzero : t • ε.symm (fOf g) = 0 := by
      apply ε.injective
      rw [map_zero]
      ext l
      rw [hall, AddEquiv.apply_symm_apply, AddMonoidHom.zero_apply]
      show g (Submodule.Quotient.mk (t • l)) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 (hN_smul t ht l), map_zero]
    rw [hzero, Submodule.coe_zero]
  let ψ : ((L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) →+ μ) → ↥A := fun g =>
    ⟨⟨((ε.symm (fOf g) : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) : J),
        hyInv_tors g⟩,
      show ((ε.symm (fOf g) : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) : J) ∈ 𝒯 from
        (Submodule.mem_inf.1 (ε.symm (fOf g)).2).1⟩
  have hyψ : ∀ g, yOf (ψ g) = ε.symm (fOf g) := fun g => Subtype.ext rfl
  let Φ : ↥A ≃ ((L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) →+ μ) :=
    { toFun := gOf
      invFun := ψ
      left_inv := fun w => by
        have h1 : fOf (gOf w) = ε (yOf w) := by
          apply AddMonoidHom.ext
          intro l
          exact gOf_mk w l
        apply Subtype.ext
        apply Subtype.ext
        show ((ε.symm (fOf (gOf w)) : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) : J)
          = ((w : ↥(heckeTorsion J 𝔪)) : J)
        rw [h1, AddEquiv.symm_apply_apply]
      right_inv := fun g => by
        apply AddMonoidHom.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | H l =>
          rw [gOf_mk, hyψ, AddEquiv.apply_symm_apply]
          rfl }

  have hpV : ∀ v : L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L)), p • v = 0 := by
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H l =>
      have h1 : ((p : HeckeAlg)) • (Submodule.Quotient.mk l : L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L)))
          = 0 := by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact hN_smul _ hpm l
      simpa only [Nat.cast_smul_eq_nsmul] using h1

  haveI hLfg : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI hVfg : AddGroup.FG (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) :=
    AddGroup.fg_of_surjective (f := (𝔪 • (⊤ : Submodule HeckeAlg L)).mkQ.toAddMonoidHom)
      (Submodule.mkQ_surjective _)
  obtain ⟨hVfin, hHomfin, hcardHomV⟩ :=
    @card_hom_eq_card_of_prime_torsion (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) μ _ _ hVfg p
      (AddCommGroup.zmodModule hpV) hp hpV hμ
  haveI := hVfin
  haveI := hHomfin
  haveI : Finite ↥A := Finite.of_equiv _ Φ.symm
  have hcards : Nat.card ↥A = Nat.card (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) := by
    rw [Nat.card_congr Φ, hcardHomV]

  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  exact finrank_eq_of_natCard_eq (HeckeAlg ⧸ 𝔪) hcards

end RibetLevelLowering

set_option pp.funBinderTypes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 20000

set_option autoImplicit false
open ModularCurve
open RibetLevelLowering

theorem solution
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    (𝒯 : Submodule HeckeAlg J) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    {p : ℕ} (hp : p.Prime) (hpm : (p : HeckeAlg) ∈ 𝔪)
    {L : Type*} [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    {μ : Type*} [AddCommGroup μ] (hμ : Nat.card μ = p)
    (ε : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg)) ≃+ (L →+ μ))
    (hε : ∀ (ℓ : Nat.Primes) (y : ↥(𝒯 ⊓ Submodule.torsionBy HeckeAlg J (p : HeckeAlg))) (l : L),
      ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l)) :
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J))) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) := by
  exact RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality 𝒯 𝔪 hp hpm hμ ε hε

end S_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality
end P2MW
export P2MW.S_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality (solution)
