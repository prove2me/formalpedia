-- Prove2me | solution 1 for Subring.eq_of_isMaximal_of_marked_galois_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/719f318a-d119-51d2-9cb3-c6d4bb69bc6e

import Mathlib
import Theorems.Thm_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subring_eq_of_isMaximal_of_marked_galois_descent
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {Ω : Type*} [Field Ω] (R₀ : Subring Ω) (F₀ Λ : Subfield Ω) (φ : Ω →+* Ω)
    (hRF : R₀ ≤ F₀.toSubring)
    (hfrac : ∀ x ∈ F₀, ∃ y z : Ω, y ∈ R₀ ∧ z ∈ R₀ ∧ z ≠ 0 ∧ x * z = y)
    (hFL : ∀ x ∈ F₀, φ x ∈ Λ)
    (S : Set Ω) (hS : S.Finite) (hSL : S ⊆ Λ) (hSint : ∀ s ∈ S, (φ.comp R₀.subtype).IsIntegralElem s)
    (hgen : Λ ≤ Subfield.closure ((F₀.map φ : Set Ω) ∪ S))
    (T : Subring Ω) (hTL : T ≤ Λ.toSubring) (hTS : T ≤ Subring.closure ((R₀.map φ : Set Ω) ∪ S))
    {ι : Type*} (G : ι → Set Ω) (hGT : ∀ i, G i ⊆ T)
    (cov : ∀ (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (_hRB : ∀ x ∈ R₀, φ x ∈ B') (hTB : T ≤ B')
      (_hint : ∀ x ∈ B', (φ.comp R₀.subtype).IsIntegralElem x) (N : Ideal ↥B'), N.IsMaximal →
      ∃ i, ∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ N)
    (uniq : ∀ (i : ι) (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (_hRB : ∀ x ∈ R₀, φ x ∈ B') (hTB : T ≤ B')
      (_hint : ∀ x ∈ B', (φ.comp R₀.subtype).IsIntegralElem x) (P₁ P₂ : Ideal ↥B'), P₁.IsPrime → P₂.IsPrime →
      (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ P₁) →
      (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ P₂) → P₁ = P₂)
    (trans : ∀ i j : ι, ∃ σ : ↥Λ ≃+* ↥Λ,
      (∀ x : ↥Λ, (x : Ω) ∈ F₀.map φ → σ x = x) ∧
      ∀ (B' : Subring Ω) (hBL : B' ≤ Λ.toSubring) (hTB : T ≤ B')
        (hσB : ∀ (b : Ω) (hb : b ∈ B'), ((σ ⟨b, hBL hb⟩ : ↥Λ) : Ω) ∈ B') (I : Ideal ↥B'),
        (∀ (g : Ω) (hg : g ∈ G i), (⟨g, hTB (hGT i hg)⟩ : ↥B') ∈ I) →
        ∀ (g : Ω) (hg : g ∈ G j), (⟨((σ ⟨g, hBL (hTB (hGT j hg))⟩ : ↥Λ) : Ω), hσB _ (hTB (hGT j hg))⟩ : ↥B') ∈ I)
    (B : Subring Ω) (hRB : R₀ ≤ B) (hBF : B ≤ F₀.toSubring) (hBint : ∀ x ∈ B, IsIntegral ↥R₀ x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsMaximal] [P₂.IsMaximal] :
    P₁ = P₂ := by
  classical

  let iRF : ↥R₀ →+* ↥F₀ := R₀.subtype.codRestrict F₀ (fun r => hRF r.2)
  let iFL : ↥F₀ →+* ↥Λ := (φ.comp F₀.subtype).codRestrict Λ (fun z => hFL z z.2)
  letI algRF : Algebra ↥R₀ ↥F₀ := iRF.toAlgebra
  letI algFL : Algebra ↥F₀ ↥Λ := iFL.toAlgebra
  letI algRL : Algebra ↥R₀ ↥Λ := (iFL.comp iRF).toAlgebra
  haveI : IsScalarTower ↥R₀ ↥F₀ ↥Λ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥R₀ ↥F₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRF_apply : ∀ r : ↥R₀, ((algebraMap ↥R₀ ↥F₀ r : ↥F₀) : Ω) = (r : Ω) := fun _ => rfl
  have hFL_apply : ∀ f : ↥F₀, ((algebraMap ↥F₀ ↥Λ f : ↥Λ) : Ω) = φ (f : Ω) := fun _ => rfl
  have hRL_apply : ∀ r : ↥R₀, ((algebraMap ↥R₀ ↥Λ r : ↥Λ) : Ω) = φ (r : Ω) := fun _ => rfl
  have hRL_comp : Λ.subtype.comp (algebraMap ↥R₀ ↥Λ) = φ.comp R₀.subtype := RingHom.ext fun _ => rfl

  haveI : IsFractionRing ↥R₀ ↥F₀ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hy0 : (y : Ω) ≠ 0 := by
        intro h
        have : y = 0 := Subtype.ext h
        rw [this] at hy
        exact zero_notMem_nonZeroDivisors hy
      refine isUnit_iff_ne_zero.mpr ?_
      intro h
      exact hy0 (congrArg Subtype.val h)
    · intro z
      obtain ⟨y, w, hy, hw, hw0, hzw⟩ := hfrac z z.2
      refine ⟨(⟨y, hy⟩, ⟨⟨w, hw⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), Subtype.ext hzw⟩
      intro h
      exact hw0 (congrArg Subtype.val h)
    · intro x y hxy
      refine ⟨1, ?_⟩
      have h' : (x : Ω) = (y : Ω) := by
        have := congrArg (fun z : ↥F₀ => (z : Ω)) hxy
        exact this
      rw [Subtype.ext h']

  have hSint' : ∀ (s : Ω) (hsS : s ∈ S) (hs : s ∈ Λ), IsIntegral ↥R₀ (⟨s, hs⟩ : ↥Λ) := by
    intro s hsS hs
    obtain ⟨p, hp, hp0⟩ := hSint s hsS
    refine ⟨p, hp, ?_⟩
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ p (algebraMap ↥R₀ ↥Λ) Λ.subtype ⟨s, hs⟩
    rw [hRL_comp] at h
    show ((Polynomial.eval₂ (algebraMap ↥R₀ ↥Λ) ⟨s, hs⟩ p : ↥Λ) : Ω) = ((0 : ↥Λ) : Ω)
    exact h.trans hp0

  let S' : Set ↥Λ := Subtype.val ⁻¹' S
  have hS'fin : S'.Finite := hS.preimage Subtype.val_injective.injOn
  have hS'int : ∀ z ∈ S', IsIntegral ↥F₀ z := fun z hz =>
    (hSint' z.1 hz z.2).tower_top
  let Sadj : Subalgebra ↥F₀ ↥Λ := Algebra.adjoin ↥F₀ S'
  haveI : Algebra.IsIntegral ↥F₀ ↥Sadj := Algebra.IsIntegral.adjoin hS'int
  have hinv : ∀ z : ↥Λ, z ∈ Sadj → z⁻¹ ∈ Sadj := by
    intro z hz
    have hzi : IsIntegral ↥F₀ (⟨z, hz⟩ : ↥Sadj) := Algebra.IsIntegral.isIntegral _
    have hzi' : IsIntegral ↥F₀ z := hzi.map Sadj.val
    exact Sadj.inv_mem_of_algebraic (x := ⟨z, hz⟩) hzi'.isAlgebraic
  let E : IntermediateField ↥F₀ ↥Λ := Sadj.toIntermediateField hinv
  let EΩ : Subfield Ω := E.toSubfield.map Λ.subtype
  have hgen' : Subfield.closure ((F₀.map φ : Set Ω) ∪ S) ≤ EΩ := by
    rw [Subfield.closure_le]
    rintro w (hw | hw)
    · obtain ⟨v, hv, rfl⟩ := (Subfield.mem_map.mp hw)
      exact ⟨algebraMap ↥F₀ ↥Λ ⟨v, hv⟩, E.algebraMap_mem _, rfl⟩
    · exact ⟨⟨w, hSL hw⟩, Algebra.subset_adjoin (show (⟨w, hSL hw⟩ : ↥Λ) ∈ S' from hw), rfl⟩
  have htop : Sadj = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨v, hv, hvz⟩ := hgen' (hgen z.2)
    have : v = z := Subtype.ext hvz
    rw [← this]
    exact hv
  haveI : FiniteDimensional ↥F₀ ↥Λ := by
    rw [FiniteDimensional, Module.finite_def, ← Algebra.top_toSubmodule, ← htop]
    exact fg_adjoin_of_finite hS'fin hS'int

  have key : IsLocalRing ↥(integralClosure ↥R₀ ↥F₀) := by
    apply integralClosure.isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
      (R := ↥R₀) (F := ↥F₀) (L := ↥Λ)
    intro M₁ M₂ hM₁ hM₂
    haveI := hM₁
    haveI := hM₂
    let C : Subalgebra ↥R₀ ↥Λ := integralClosure ↥R₀ ↥Λ
    let B' : Subring Ω := (C.toSubring).map Λ.subtype
    have hmemB' : ∀ {w : Ω} (hw : w ∈ Λ), w ∈ B' ↔ IsIntegral ↥R₀ (⟨w, hw⟩ : ↥Λ) := by
      intro w hw
      constructor
      · rintro ⟨c, hc, hcw⟩
        have : c = ⟨w, hw⟩ := Subtype.ext hcw
        rw [← this]; exact hc
      · intro h; exact ⟨⟨w, hw⟩, h, rfl⟩
    have hBL : B' ≤ Λ.toSubring := by
      rintro _ ⟨c, -, rfl⟩; exact c.2
    have hRB : ∀ r ∈ R₀, φ r ∈ B' := fun r hr =>
      ⟨algebraMap ↥R₀ ↥Λ ⟨r, hr⟩, C.algebraMap_mem _, rfl⟩
    have hTB : T ≤ B' := by
      refine hTS.trans ?_
      rw [Subring.closure_le]
      rintro w (hw | hw)
      · obtain ⟨r, hr, rfl⟩ := (Subring.mem_map.mp hw)
        exact hRB r hr
      · exact (hmemB' (hSL hw)).mpr (hSint' w hw _)
    have hint' : ∀ w ∈ B', (φ.comp R₀.subtype).IsIntegralElem w := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨p, hp, hp0⟩ := (hc : IsIntegral ↥R₀ c)
      refine ⟨p, hp, ?_⟩
      have h := Polynomial.hom_eval₂ p (algebraMap ↥R₀ ↥Λ) Λ.subtype c
      rw [hRL_comp] at h
      rw [← h, hp0, map_zero]

    let e : ↥C ≃+* ↥B' := C.toSubring.equivMapOfInjective Λ.subtype Subtype.val_injective
    have he : ∀ c : ↥C, ((e c : ↥B') : Ω) = ((c : ↥Λ) : Ω) := fun _ => rfl
    let N₁ : Ideal ↥B' := M₁.comap e.symm.toRingHom
    let N₂ : Ideal ↥B' := M₂.comap e.symm.toRingHom
    haveI hN₁ : N₁.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    haveI hN₂ : N₂.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    obtain ⟨i, hi⟩ := cov B' hBL hRB hTB hint' N₁ hN₁
    obtain ⟨j, hj⟩ := cov B' hBL hRB hTB hint' N₂ hN₂
    obtain ⟨σ, hfix, htr⟩ := trans i j
    have hfixF : ∀ f : ↥F₀, σ (algebraMap ↥F₀ ↥Λ f) = algebraMap ↥F₀ ↥Λ f := fun f =>
      hfix _ (Subfield.mem_map.mpr ⟨f, f.2, rfl⟩)
    let σ' : ↥Λ ≃ₐ[↥F₀] ↥Λ := { σ with commutes' := hfixF }
    have hσ' : ∀ z : ↥Λ, σ' z = σ z := fun _ => rfl
    refine ⟨σ', ?_⟩

    have hσB : ∀ (b : Ω) (hb : b ∈ B'), ((σ ⟨b, hBL hb⟩ : ↥Λ) : Ω) ∈ B' := by
      intro b hb
      have hbI : IsIntegral ↥R₀ (⟨b, hBL hb⟩ : ↥Λ) := (hmemB' (hBL hb)).mp hb
      have := hbI.map (σ'.toAlgHom.restrictScalars ↥R₀)
      exact ⟨σ ⟨b, hBL hb⟩, this, rfl⟩
    let σB : ↥B' →+* ↥B' :=
      { toFun := fun b => ⟨(σ ⟨b, hBL b.2⟩ : Ω), hσB b b.2⟩
        map_one' := by
          apply Subtype.ext
          show ((σ ⟨((1 : ↥B') : Ω), _⟩ : ↥Λ) : Ω) = 1
          rw [show (⟨((1 : ↥B') : Ω), hBL (1 : ↥B').2⟩ : ↥Λ) = 1 from rfl, map_one]; rfl
        map_mul' := fun b b' => by
          apply Subtype.ext
          show ((σ ⟨((b * b' : ↥B') : Ω), _⟩ : ↥Λ) : Ω) = ((σ ⟨(b : Ω), _⟩ : ↥Λ) : Ω) * ((σ ⟨(b' : Ω), _⟩ : ↥Λ) : Ω)
          rw [show (⟨((b * b' : ↥B') : Ω), hBL (b * b').2⟩ : ↥Λ) = ⟨(b : Ω), hBL b.2⟩ * ⟨(b' : Ω), hBL b'.2⟩ from rfl,
            map_mul]; rfl
        map_zero' := by
          apply Subtype.ext
          show ((σ ⟨((0 : ↥B') : Ω), _⟩ : ↥Λ) : Ω) = 0
          rw [show (⟨((0 : ↥B') : Ω), hBL (0 : ↥B').2⟩ : ↥Λ) = 0 from rfl, map_zero]; rfl
        map_add' := fun b b' => by
          apply Subtype.ext
          show ((σ ⟨((b + b' : ↥B') : Ω), _⟩ : ↥Λ) : Ω) = ((σ ⟨(b : Ω), _⟩ : ↥Λ) : Ω) + ((σ ⟨(b' : Ω), _⟩ : ↥Λ) : Ω)
          rw [show (⟨((b + b' : ↥B') : Ω), hBL (b + b').2⟩ : ↥Λ) = ⟨(b : Ω), hBL b.2⟩ + ⟨(b' : Ω), hBL b'.2⟩ from rfl,
            map_add]; rfl }
    have hσB_apply : ∀ b : ↥B', ((σB b : ↥B') : Ω) = ((σ ⟨b, hBL b.2⟩ : ↥Λ) : Ω) := fun _ => rfl

    haveI : (N₁.comap σB).IsPrime := Ideal.IsPrime.comap σB
    have hN : N₂ = N₁.comap σB :=
      uniq j B' hBL hRB hTB hint' N₂ (N₁.comap σB) inferInstance inferInstance hj
        (fun g hg => by rw [Ideal.mem_comap]; exact htr B' hBL hTB hσB N₁ hi g hg)

    ext c
    have h1 : c ∈ M₂ ↔ e c ∈ N₂ := by
      show c ∈ M₂ ↔ e.symm.toRingHom (e c) ∈ M₂
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    have h2 : c ∈ Ideal.comap (galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ') M₁ ↔ e (galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ' c) ∈ N₁ := by
      rw [Ideal.mem_comap]
      show _ ↔ e.symm.toRingHom (e _) ∈ M₁
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    rw [h1, h2, hN, Ideal.mem_comap]
    have h3 : σB (e c) = e (galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ' c) := by
      apply Subtype.ext
      have h5 : (⟨(e c : Ω), hBL (e c).2⟩ : ↥Λ) = (c : ↥Λ) := Subtype.ext (he c)
      have h4 := algebraMap_galRestrict_apply ↥R₀ (K := ↥F₀) (L := ↥Λ) (B := ↥C) σ' c

      change ((galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ' c : ↥C) : ↥Λ) = σ' (c : ↥Λ) at h4
      calc ((σB (e c) : ↥B') : Ω) = ((σ ⟨(e c : Ω), hBL (e c).2⟩ : ↥Λ) : Ω) := rfl
        _ = ((σ (c : ↥Λ) : ↥Λ) : Ω) := congrArg (fun z => ((σ z : ↥Λ) : Ω)) h5
        _ = ((σ' (c : ↥Λ) : ↥Λ) : Ω) := rfl
        _ = (((galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ' c : ↥C) : ↥Λ) : Ω) := by rw [h4]
        _ = ((e (galRestrict ↥R₀ ↥F₀ ↥Λ ↥C σ' c) : ↥B') : Ω) := (he _).symm
    rw [h3]

  let C₀ := integralClosure ↥R₀ ↥F₀
  haveI := key

  let iBC : ↥B →+* ↥C₀ :=
    { toFun := fun b => ⟨⟨(b : Ω), hBF b.2⟩, by
        have hb := hBint b b.2

        have hinj : Function.Injective (IsScalarTower.toAlgHom ↥R₀ ↥F₀ Ω) := Subtype.val_injective
        exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥R₀ ↥F₀ Ω) hinj).mp hb⟩
      map_one' := Subtype.ext (Subtype.ext rfl)
      map_mul' := fun _ _ => Subtype.ext (Subtype.ext rfl)
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
  letI algBC : Algebra ↥B ↥C₀ := iBC.toAlgebra
  letI algRB : Algebra ↥R₀ ↥B := (Subring.inclusion hRB).toAlgebra
  haveI : IsScalarTower ↥R₀ ↥B ↥C₀ := IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext (Subtype.ext rfl))
  haveI : Algebra.IsIntegral ↥B ↥C₀ := ⟨fun c => (integralClosure.isIntegral c).tower_top⟩
  have hinjBC : Function.Injective (algebraMap ↥B ↥C₀) := fun b b' h =>
    Subtype.ext (congrArg (fun z : ↥C₀ => ((z : ↥F₀) : Ω)) h)
  have hker : ∀ P : Ideal ↥B, RingHom.ker (algebraMap ↥B ↥C₀) ≤ P := fun P => by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjBC]; exact bot_le
  obtain ⟨Q₁, hQ₁, hQ₁P⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P₁ (hker P₁)
  obtain ⟨Q₂, hQ₂, hQ₂P⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P₂ (hker P₂)
  rw [← hQ₁P, ← hQ₂P, IsLocalRing.eq_maximalIdeal hQ₁, IsLocalRing.eq_maximalIdeal hQ₂]

end S_Subring_eq_of_isMaximal_of_marked_galois_descent
end P2MW
export P2MW.S_Subring_eq_of_isMaximal_of_marked_galois_descent (solution)
