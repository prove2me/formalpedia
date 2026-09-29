-- Prove2me | solution 1 for PDivisibleGroup.ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/885ffff7-3eee-5154-a62a-b3bfb530c95b

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_finrank_quotient_span_pow_augIdeal_eq_pow_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe v

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.augIdeal Hopf.mem_augIdeal_iff Hopf.sub_algebraMap_counit_mem_augIdeal Hopf.torsionIdeal height level mk finrank_quotient_span_pow_augIdeal_eq_pow_of_isLocalRing"
namespace C1Coords
p2m_open "PDivisibleGroup"

open MvPolynomial

section Trunc

variable (k : Type*) [Field k] (d m : ℕ)

private noncomputable def truncIdeal : Ideal (MvPolynomial (Fin d) k) :=
  Ideal.span (Set.range fun i : Fin d => (X i : MvPolynomial (Fin d) k) ^ m)

private theorem monomial_mem_truncIdeal {α : Fin d →₀ ℕ} {i : Fin d} (hi : m ≤ α i) (c : k) :
    monomial α c ∈ truncIdeal k d m := by
  classical
  have hα : (α - Finsupp.single i m) + Finsupp.single i m = α := by
    ext j
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  have : monomial α c = monomial (α - Finsupp.single i m) c * X i ^ m := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hα]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

private noncomputable def smallMon (g : Fin d → Fin m) : MvPolynomial (Fin d) k :=
  monomial (Finsupp.equivFunOnFinite.symm fun i => (g i : ℕ)) 1

private theorem span_mk_smallMon :
    Submodule.span k (Set.range fun g : Fin d → Fin m =>
      Ideal.Quotient.mkₐ k (truncIdeal k d m) (smallMon k d m g)) = ⊤ := by
  classical
  have key : ∀ f : MvPolynomial (Fin d) k, Ideal.Quotient.mkₐ k (truncIdeal k d m) f ∈
      Submodule.span k (Set.range fun g : Fin d → Fin m =>
        Ideal.Quotient.mkₐ k (truncIdeal k d m) (smallMon k d m g)) := by
    intro f
    induction f using MvPolynomial.induction_on' with
    | monomial α c =>
      by_cases h : ∀ i, α i < m
      · have hαc : monomial α c = c • smallMon k d m (fun i => ⟨α i, h i⟩) := by
          rw [smallMon, smul_monomial, smul_eq_mul, mul_one]
          congr 1
          ext i
          simp
        rw [hαc, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · push Not at h
        obtain ⟨i, hi⟩ := h
        have h0 : Ideal.Quotient.mkₐ k (truncIdeal k d m) (monomial α c) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (monomial_mem_truncIdeal k d m hi c)
        rw [h0]
        exact Submodule.zero_mem _
    | add f g hf hg =>
      rw [map_add]
      exact Submodule.add_mem _ hf hg
  rw [eq_top_iff]
  rintro y -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ y
  exact key f

private theorem finite_and_finrank_quotient_truncIdeal_le :
    Module.Finite k (MvPolynomial (Fin d) k ⧸ truncIdeal k d m) ∧
    Module.finrank k (MvPolynomial (Fin d) k ⧸ truncIdeal k d m) ≤ m ^ d := by
  classical
  have hspan := span_mk_smallMon k d m
  refine ⟨⟨?_⟩, ?_⟩
  · rw [← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  · have h := finrank_range_le_card (R := k) (fun g : Fin d → Fin m =>
      Ideal.Quotient.mkₐ k (truncIdeal k d m) (smallMon k d m g))
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact h

end Trunc

section Gen

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

private theorem aeval_surjective_of_span_toCotangent_eq_top
    (I : Ideal A) (hfg : I.FG) (hjac : I ≤ Ideal.jacobson ⊥) (N : ℕ) (hnil : I ^ N = ⊥)
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ I)
    {ι : Type*} (x : ι → A) (hx : ∀ i, x i ∈ I)
    (hspan : Submodule.span k (Set.range fun i => I.toCotangent ⟨x i, hx i⟩) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] A) := by
  classical

  let x' : ι → I := fun i => ⟨x i, hx i⟩
  have H : (Submodule.span A (Set.range x')).map I.toCotangent = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.restrictScalars_eq_top_iff k, eq_top_iff,
      ← hspan]
    exact Submodule.span_le_restrictScalars k A _
  have h1 : Submodule.span A (Set.range x') = ⊤ := by
    refine eq_top_iff.mpr ?_
    refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype I) _ _).mp ?_
    rw [Submodule.map_top, Submodule.range_subtype]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac
    rw [smul_eq_mul, ← pow_two, ← Ideal.map_toCotangent_ker, ← Submodule.map_sup,
      ← Submodule.comap_map_eq, H, Submodule.comap_top, Submodule.map_top, Submodule.range_subtype]
  have h2 : ∀ a ∈ I, a ∈ Submodule.span A (Set.range x) := by
    intro a ha
    have ha' : (⟨a, ha⟩ : I) ∈ Submodule.span A (Set.range x') := by
      rw [h1]
      exact Submodule.mem_top
    have h := Submodule.mem_map_of_mem (f := I.subtype) ha'
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

  let T : Submodule k A := Subalgebra.toSubmodule (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] A).range
  have hxT : ∀ i, x i ∈ T := fun i => ⟨MvPolynomial.X i, MvPolynomial.aeval_X x i⟩
  have hmulT : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := fun a ha b hb => Subalgebra.mul_mem _ ha hb
  have halgT : ∀ c : k, algebraMap k A c ∈ T := fun c => Subalgebra.algebraMap_mem _ c
  have hP : ∀ n : ℕ, (I ^ n).restrictScalars k ≤ T ⊔ (I ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro a _
      obtain ⟨c, hc⟩ := hres a
      have hdec : a = algebraMap k A c + (a - algebraMap k A c) := by ring
      rw [hdec]
      refine Submodule.add_mem_sup (halgT c) ?_
      rw [Submodule.restrictScalars_mem, zero_add, pow_one]
      exact hc
    | succ n ih =>
      intro a ha
      rw [Submodule.restrictScalars_mem, pow_succ'] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro a ha b hb
        refine Submodule.span_induction
          (p := fun a _ => ∀ b ∈ I ^ n, a * b ∈ T ⊔ (I ^ (n + 1 + 1)).restrictScalars k)
          ?_ ?_ ?_ ?_ (h2 a ha) b hb
        · rintro _ ⟨i, rfl⟩ b hb
          obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.mp (ih hb)
          rw [← htc, mul_add]
          refine Submodule.add_mem_sup (hmulT _ (hxT i) _ ht) ?_
          rw [Submodule.restrictScalars_mem, pow_succ']
          exact Ideal.mul_mem_mul (hx i) hc
        · intro b _
          rw [zero_mul]
          exact Submodule.zero_mem _
        · intro a₁ a₂ _ _ h₁ h₂ b hb
          rw [add_mul]
          exact Submodule.add_mem _ (h₁ b hb) (h₂ b hb)
        · intro r a _ h b hb
          rw [smul_eq_mul, mul_assoc, mul_left_comm]
          exact h (r * b) (Ideal.mul_mem_left _ r hb)
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb

  have hP' : ∀ j n : ℕ, (I ^ n).restrictScalars k ≤ T ⊔ (I ^ (n + j)).restrictScalars k := by
    intro j
    induction j with
    | zero =>
      intro n
      rw [add_zero]
      exact le_sup_right
    | succ j ih =>
      intro n
      calc (I ^ n).restrictScalars k ≤ T ⊔ (I ^ (n + j)).restrictScalars k := ih n
        _ ≤ T ⊔ (T ⊔ (I ^ (n + j + 1)).restrictScalars k) := sup_le_sup_left (hP (n + j)) T
        _ = T ⊔ (I ^ (n + (j + 1))).restrictScalars k := by rw [← sup_assoc, sup_idem, add_assoc]
  have htop : ∀ a : A, a ∈ T := by
    intro a
    have h := hP' N 0
    rw [pow_zero, Ideal.one_eq_top, zero_add, hnil, Submodule.restrictScalars_top,
      Submodule.restrictScalars_bot, sup_bot_eq, top_le_iff] at h
    rw [h]
    exact Submodule.mem_top
  intro a
  obtain ⟨f, hf⟩ := htop a
  exact ⟨f, hf⟩

end Gen

end PDivisibleGroup.C1Coords

theorem solution
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (n w : ℕ) (hnw : n ≤ w) (d : ℕ)
    (hd : Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent = d)
    (x : Fin d → H w) (hx : ∀ i, x i ∈ PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w))
    (hspan : Submodule.span (ZMod p) (Set.range fun i =>
      (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)).toCotangent ⟨x i, hx i⟩) = ⊤) :
    Function.Surjective ((Ideal.Quotient.mkₐ (ZMod p) (Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))))).comp
        (MvPolynomial.aeval x)) ∧
    RingHom.ker ((Ideal.Quotient.mkₐ (ZMod p) (Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))))).comp
        (MvPolynomial.aeval x) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] _) =
      Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ p ^ n) := by
  classical
  obtain ⟨hp⟩ := ‹Fact p.Prime›
  haveI := hlocH w

  have hsurj : Function.Surjective
      (MvPolynomial.aeval x : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H w) := by
    haveI : IsArtinianRing (H w) := IsArtinianRing.of_finite (ZMod p) (H w)
    have hItop : PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) ≠ ⊤ := by
      intro h
      have h1 : (1 : H w) ∈ PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) := h ▸ Submodule.mem_top
      rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, Bialgebra.counit_one] at h1
      exact one_ne_zero h1
    have hjac : PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) ≤ Ideal.jacobson ⊥ := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hItop
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := H w)
    have hnil : PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) ^ N = ⊥ := by
      have h := Ideal.pow_right_mono hjac N
      rw [hN, Submodule.zero_eq_bot, le_bot_iff] at h
      exact h
    exact PDivisibleGroup.C1Coords.aeval_surjective_of_span_toCotangent_eq_top
      (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w)) (IsNoetherian.noetherian _) hjac N hnil
      (fun a => ⟨_, PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal (ZMod p) (H w) a⟩)
      x hx hspan
  set J : Ideal (H w) := Ideal.span ((fun a : H w => a ^ p ^ n) ''
    (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))) with hJ
  set ψ : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H w ⧸ J :=
    (Ideal.Quotient.mkₐ (ZMod p) J).comp (MvPolynomial.aeval x) with hψ
  have hψsurj : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective (ZMod p) J).comp hsurj
  refine ⟨hψsurj, ?_⟩

  have hKle : PDivisibleGroup.C1Coords.truncIdeal (ZMod p) d (p ^ n) ≤ RingHom.ker ψ := by
    rw [PDivisibleGroup.C1Coords.truncIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hψ, AlgHom.comp_apply, map_pow, MvPolynomial.aeval_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨x i, hx i, rfl⟩)

  obtain ⟨hfinV, hdimV⟩ :=
    PDivisibleGroup.C1Coords.finite_and_finrank_quotient_truncIdeal_le (ZMod p) d (p ^ n)
  have hdimW : Module.finrank (ZMod p) (H w ⧸ J) = p ^ (n * d) := by
    have h := PDivisibleGroup.finrank_quotient_span_pow_augIdeal_eq_pow_of_isLocalRing p h₀ H s hs
      hrankH hkerH hlocH n w hnw
    rw [hd] at h
    exact h
  haveI : Module.Finite (ZMod p) (H w ⧸ J) := inferInstance
  let ψbar : (MvPolynomial (Fin d) (ZMod p) ⧸ PDivisibleGroup.C1Coords.truncIdeal (ZMod p) d (p ^ n))
      →ₐ[ZMod p] H w ⧸ J :=
    Ideal.Quotient.liftₐ _ ψ (fun a ha => RingHom.mem_ker.mp (hKle ha))
  have hψbar_surj : Function.Surjective ψbar := by
    intro y
    obtain ⟨f, rfl⟩ := hψsurj y
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  have hle1 : Module.finrank (ZMod p)
      (MvPolynomial (Fin d) (ZMod p) ⧸ PDivisibleGroup.C1Coords.truncIdeal (ZMod p) d (p ^ n)) ≤
      Module.finrank (ZMod p) (H w ⧸ J) := by
    rw [hdimW, pow_mul]
    exact hdimV
  have hle2 : Module.finrank (ZMod p) (H w ⧸ J) ≤ Module.finrank (ZMod p)
      (MvPolynomial (Fin d) (ZMod p) ⧸ PDivisibleGroup.C1Coords.truncIdeal (ZMod p) d (p ^ n)) := by
    have h := LinearMap.finrank_range_le ψbar.toLinearMap
    rwa [LinearMap.range_eq_top.mpr hψbar_surj, finrank_top] at h
  have hinj : Function.Injective ψbar :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ψbar.toLinearMap)
      (le_antisymm hle1 hle2)).mpr hψbar_surj

  refine le_antisymm ?_ hKle
  intro f hf
  rw [RingHom.mem_ker] at hf
  have h0 : ψbar (Ideal.Quotient.mk _ f) = ψbar 0 := by
    rw [map_zero]
    exact hf
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj h0)

end S_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
end P2MW
export P2MW.S_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing (solution)
