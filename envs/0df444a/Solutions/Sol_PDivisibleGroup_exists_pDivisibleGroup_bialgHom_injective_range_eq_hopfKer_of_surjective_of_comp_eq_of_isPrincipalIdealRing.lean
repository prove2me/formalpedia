-- Prove2me | solution 1 for PDivisibleGroup.exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/903fcea0-a952-567b-aaff-933518edc432

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_PDivisibleGroup_Tower
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
import Theorems.Thm_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
import Theorems.Thm_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct

namespace HQUOT

variable {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {h t : ℕ}
  (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
  (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
  (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v))

include hπ in

theorem finite_free_rank (v : ℕ) :
    Module.Finite R ↥(HopfAlgebra.hopfKer (π v)) ∧ Module.Free R ↥(HopfAlgebra.hopfKer (π v)) ∧
      Module.finrank R ↥(HopfAlgebra.hopfKer (π v)) * p ^ (v * t) = p ^ (v * h) := by
  obtain ⟨hret, hfin, hproj, hrank⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (π v) (hπ v)
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R ↥(HopfAlgebra.hopfKer (π v)) := Module.free_of_flat_of_isLocalRing
  refine ⟨hfin, inferInstance, ?_⟩
  have hh := hrank (IsLocalRing.closedPoint R)
  rw [Module.rankAtStalk_eq_finrank_of_free, T.finrank_level, G.finrank_level] at hh
  exact hh

include hπt in

theorem mapsTo_transition (v : ℕ) :
    Set.MapsTo (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v)) := by
  intro a ha
  rw [SetLike.mem_coe, HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply] at ha ⊢

  have hΔ : Coalgebra.comul (R := R) (G.transition v a) =
      Algebra.TensorProduct.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v)
        (G.transition v : G.level (v + 1) →ₐ[R] G.level v) (Coalgebra.comul (R := R) a) :=
    (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom (G.transition v)) a).symm
  rw [hΔ, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]

  have key : Algebra.TensorProduct.map ((AlgHom.id R (G.level v)).comp (G.transition v : G.level (v + 1) →ₐ[R] G.level v))
        ((π v : G.level v →ₐ[R] T.level v).comp (G.transition v : G.level (v + 1) →ₐ[R] G.level v)) =
      (Algebra.TensorProduct.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v) (T.transition v : T.level (v + 1) →ₐ[R] T.level v)).comp
        (Algebra.TensorProduct.map (AlgHom.id R (G.level (v + 1))) (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
    congr 1
    have := congrArg (fun f : G.level (v + 1) →ₐc[R] T.level v => (f : G.level (v + 1) →ₐ[R] T.level v)) (hπt v)
    simpa using this.symm
  rw [key, AlgHom.comp_apply, ha, Algebra.TensorProduct.map_tmul, map_one]
  rfl

include hπ hπt in

theorem surjOn_transition [IsDomain R] [IsPrincipalIdealRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] (v : ℕ) :
    Set.SurjOn (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v)) :=
  PDivisibleGroup.surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing K p G T π hπ hπt v

include hπ hπt in

theorem transition_apply_eq_zero_iff [IsDomain R] [IsPrincipalIdealRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] (v : ℕ) [Module.Flat R ↥(HopfAlgebra.hopfKer (π (v + 1)))]
    (a : ↥(HopfAlgebra.hopfKer (π (v + 1)))) :
    G.transition v (a : G.level (v + 1)) = 0 ↔
      a ∈ PDivisibleGroup.Hopf.torsionIdeal R ↥(HopfAlgebra.hopfKer (π (v + 1))) (p ^ v) :=
  PDivisibleGroup.transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing K p G T π hπ hπt v a

include hπ in
theorem t_le_h : t ≤ h := by
  have h1 := (finite_free_rank G T π hπ 1).2.2
  rw [one_mul, one_mul] at h1
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  exact (Nat.pow_dvd_pow_iff_le_right hp).mp (Dvd.intro_left _ h1)

include hπ in
theorem finrank_hopfKer (v : ℕ) : Module.finrank R ↥(HopfAlgebra.hopfKer (π v)) = p ^ (v * (h - t)) := by
  have h1 := (finite_free_rank G T π hπ v).2.2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hth := t_le_h G T π hπ
  have : p ^ (v * h) = p ^ (v * (h - t)) * p ^ (v * t) := by
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hth]
  rw [this] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp _) h1

noncomputable def transK (v : ℕ) (hmaps : Set.MapsTo (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v))) :
    ↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] ↥(HopfAlgebra.hopfKer (π v)) :=
  ((G.transition v : G.level (v + 1) →ₐ[R] G.level v).comp (HopfAlgebra.hopfKer (π (v + 1))).val).codRestrict
    (HopfAlgebra.hopfKer (π v)) (fun a => hmaps a.2)

@[scoped simp] theorem coe_transK (v : ℕ) (hmaps) (a : ↥(HopfAlgebra.hopfKer (π (v + 1)))) :
    ((transK G T π v hmaps a : ↥(HopfAlgebra.hopfKer (π v))) : G.level v) = G.transition v (a : G.level (v + 1)) := rfl

end HQUOT
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing.HQUOT"

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v)) :
    ∃ (hB : ℕ) (B : PDivisibleGroup R p hB) (j : ∀ v : ℕ, B.level v →ₐc[R] G.level v),
      h = t + hB ∧
      (∀ v, Function.Injective (j v)) ∧
      (∀ v, (j v : B.level v →ₐ[R] G.level v).range = HopfAlgebra.hopfKer (π v)) ∧
      (∀ v : ℕ, (G.transition v).comp (j (v + 1)) = (j v).comp (B.transition v)) ∧

      (∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (v : ℕ) (x : G.Point L v),
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (j v : B.level v →ₐ[R] G.level v)) =
            (1 : B.Point L v) ↔
          ∃ y : T.Point L v,
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (π v : G.level v →ₐ[R] T.level v)) = x) ∧

      (∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra R L] (v : ℕ) (b : B.Point L v), ∃ x : G.Point L v,
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (j v : B.level v →ₐ[R] G.level v)) = b) := by
  classical

  have hff := HQUOT.finite_free_rank G T π hπ
  haveI hfin : ∀ v, Module.Finite R ↥(HopfAlgebra.hopfKer (π v)) := fun v => (hff v).1
  haveI hfree : ∀ v, Module.Free R ↥(HopfAlgebra.hopfKer (π v)) := fun v => (hff v).2.1
  haveI hflat : ∀ v, Module.Flat R ↥(HopfAlgebra.hopfKer (π v)) := fun v => Module.Flat.of_free
  letI hHopf : ∀ v, HopfAlgebra R ↥(HopfAlgebra.hopfKer (π v)) := fun v => HopfAlgebra.HopfKerHopf.instHopfAlgebra (π v)
  haveI hcc : ∀ v, Coalgebra.IsCocomm R ↥(HopfAlgebra.hopfKer (π v)) := fun v => HopfAlgebra.HopfKerHopf.instIsCocomm (π v)
  have hmaps := HQUOT.mapsTo_transition G T π hπt

  let tr : ∀ v, ↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐc[R] ↥(HopfAlgebra.hopfKer (π v)) := fun v =>
    { HQUOT.transK G T π v (hmaps v) with
      map_smul' := fun r a => map_smul (HQUOT.transK G T π v (hmaps v)) r a
      counit_comp := by
        apply LinearMap.ext
        intro a
        change Coalgebra.counit (R := R) (HQUOT.transK G T π v (hmaps v) a) = Coalgebra.counit (R := R) a
        rw [HopfAlgebra.HopfKerHopf.counit_coe, HopfAlgebra.HopfKerHopf.counit_coe, HQUOT.coe_transK]
        exact PDivisibleGroup.Hopf.counit_bialgHom_apply (G.transition v) _
      map_comp_comul := by
        apply LinearMap.ext
        intro a
        change TensorProduct.map (HQUOT.transK G T π v (hmaps v)).toLinearMap (HQUOT.transK G T π v (hmaps v)).toLinearMap
            (Coalgebra.comul (R := R) a) = Coalgebra.comul (R := R) (HQUOT.transK G T π v (hmaps v) a)
        apply HopfAlgebra.HopfKerHopf.ι₂_injective (π v)
        rw [HopfAlgebra.HopfKerHopf.ι₂_eq_map, HopfAlgebra.HopfKerHopf.map_val_val_comul (π v),
          ← LinearMap.comp_apply, ← TensorProduct.map_comp]
        have hcomp : HopfAlgebra.HopfKerHopf.valL (π v) ∘ₗ (HQUOT.transK G T π v (hmaps v)).toLinearMap =
            (G.transition v : G.level (v + 1) →ₐ[R] G.level v).toLinearMap ∘ₗ HopfAlgebra.HopfKerHopf.valL (π (v + 1)) := by
          apply LinearMap.ext; intro x; rfl
        rw [hcomp, TensorProduct.map_comp, LinearMap.comp_apply, HopfAlgebra.HopfKerHopf.map_val_val_comul (π (v + 1)) a,
          HQUOT.coe_transK]
        exact CoalgHomClass.map_comp_comul_apply (G.transition v) (a : G.level (v + 1)) }

  have hth : t ≤ h := HQUOT.t_le_h G T π hπ
  let B : PDivisibleGroup R p (h - t) :=
    { level := fun v => ↥(HopfAlgebra.hopfKer (π v))
      transition := tr
      transition_surjective := fun v => by
        intro b
        obtain ⟨a, ha, hab⟩ := HQUOT.surjOn_transition G T π hπ hπt K v b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
      finrank_level := fun v => HQUOT.finrank_hopfKer G T π hπ v
      ker_transition := fun v => by
        ext a
        rw [RingHom.mem_ker]
        change tr v a = 0 ↔ _
        rw [← HQUOT.transition_apply_eq_zero_iff G T π hπ hπt K v a]
        constructor
        · intro h0; exact congrArg Subtype.val h0
        · intro h0; exact Subtype.ext h0 }
  let j : ∀ v : ℕ, B.level v →ₐc[R] G.level v := fun v => HopfAlgebra.HopfKerHopf.hopfKerVal (π v)
  have hjval : ∀ v, (j v : B.level v →ₐ[R] G.level v) = (HopfAlgebra.hopfKer (π v)).val := fun v => AlgHom.ext fun _ => rfl
  refine ⟨h - t, B, j, (Nat.add_sub_cancel' hth).symm, fun v => Subtype.val_injective, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · rw [hjval]; exact Subalgebra.range_val _
  · apply BialgHom.coe_algHom_injective
    apply AlgHom.ext; intro a; rfl
  ·
    intro L _ _ _ v x
    have h9 := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique (π v) (hπ v) L
    rw [hjval]

    have key : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (HopfAlgebra.hopfKer (π v)).val) =
          (1 : B.Point L v) ↔
        (WithConv.ofConv (1 : WithConv (G.level v →ₐ[R] L))).comp (HopfAlgebra.hopfKer (π v)).val =
          (WithConv.ofConv (PDivisibleGroup.Point.toConv x)).comp (HopfAlgebra.hopfKer (π v)).val := by
      have h1 : (1 : B.Point L v) = PDivisibleGroup.Point.ofConv
          (WithConv.toConv ((WithConv.ofConv (1 : WithConv (G.level v →ₐ[R] L))).comp (HopfAlgebra.hopfKer (π v)).val)) := by
        rw [h9.1]; rfl
      rw [h1]
      constructor
      · intro hh
        exact (congrArg PDivisibleGroup.Point.toAlgHom hh).symm
      · intro hh
        exact congrArg PDivisibleGroup.Point.ofAlgHom hh.symm
    rw [key, h9.2.2]
    constructor
    · rintro ⟨χ, hχ, -⟩
      refine ⟨PDivisibleGroup.Point.ofAlgHom χ, ?_⟩
      rw [one_mul] at hχ
      apply PDivisibleGroup.Point.ext
      intro a
      have := congrArg (fun z : WithConv (G.level v →ₐ[R] L) => WithConv.ofConv z a) hχ
      exact this.symm
    · rintro ⟨y, rfl⟩
      refine ⟨PDivisibleGroup.Point.toAlgHom y, ?_, ?_⟩
      · change _ = (1 : WithConv (G.level v →ₐ[R] L)) * _
        rw [one_mul]; rfl
      · intro χ hχ
        rw [one_mul] at hχ
        apply AlgHom.ext
        intro b
        obtain ⟨a, rfl⟩ := hπ v b
        have := congrArg (fun z : WithConv (G.level v →ₐ[R] L) => WithConv.ofConv z a) hχ
        exact this.symm
  ·
    intro L _ _ _ v b
    obtain ⟨ν, hν⟩ := Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite (HopfAlgebra.hopfKer (π v)) L
      (PDivisibleGroup.Point.toAlgHom b)
    refine ⟨PDivisibleGroup.Point.ofAlgHom ν, ?_⟩
    rw [hjval]
    apply PDivisibleGroup.Point.ext
    intro a
    exact congrArg (fun f : ↥(HopfAlgebra.hopfKer (π v)) →ₐ[R] L => f a) hν

end S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
end P2MW
export P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_injective_range_eq_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing (solution)
