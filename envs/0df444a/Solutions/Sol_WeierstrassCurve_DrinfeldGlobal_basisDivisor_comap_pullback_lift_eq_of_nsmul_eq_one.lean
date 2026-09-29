-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/35731285-8970-54eb-a6c7-88bbe45292b3

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra WeierstrassCurve.DrinfeldGlobal

namespace DivShiftAsm

universe u

section IsoComap
variable {X Y : Scheme.{u}}

theorem comap_hom_eq_map_inv (I : Y.IdealSheafData) (e : X ≅ Y) : I.comap e.hom = I.map e.inv := by
  show (pullback.fst e.hom I.subschemeι).ker = (I.subschemeι ≫ e.inv).ker
  have h : pullback.fst e.hom I.subschemeι = pullback.snd e.hom I.subschemeι ≫ (I.subschemeι ≫ e.inv) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

theorem comap_ker_hom {T : Scheme.{u}} (γ : T ⟶ Y) (e : X ≅ Y) : γ.ker.comap e.hom = (γ ≫ e.inv).ker := by
  rw [comap_hom_eq_map_inv, Scheme.IdealSheafData.map_ker]

theorem comap_mul_of_isOpenImmersion (I J : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e := (f.appIso U).commRingCatIsoToRingEquiv
  have he : ∀ A : Ideal _, Ideal.comap (f.appIso U).inv.hom A = Ideal.map e A := fun A => by
    rw [← Ideal.comap_symm]
    ext x
    simp only [Ideal.mem_comap]
    rfl
  rw [he, he, he, Ideal.map_mul]

theorem comap_prod_of_isOpenImmersion {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (∏ i, I i).comap f = ∏ i, (I i).comap f := by
  show (∏ i ∈ Finset.univ, I i).comap f = ∏ i ∈ Finset.univ, (I i).comap f
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp [Scheme.IdealSheafData.comap_top]
  | cons i s hi ih => rw [Finset.prod_cons, Finset.prod_cons, comap_mul_of_isOpenImmersion, ih]

end IsoComap

section Graph
universe v
variable {𝒞 S : Scheme.{v}} (f : 𝒞 ⟶ S) {T' : Scheme.{v}} {g : T' ⟶ S}

theorem graphOver_ker_congr (c c' : SchemeHomOver g f) (h : c = c') :
    (graphOver f c.1 c.2).ker = (graphOver f c'.1 c'.2).ker := by
  subst h; rfl

end Graph

end DivShiftAsm

open DivShiftAsm in
theorem solution
    {T : Type} [CommRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ)
    (P Q : Section W) (hQ : G.nsmul (𝟙 (base (T := T))) q Q = G.one (𝟙 (base (T := T))))
    (τ : projModelCR W ≅ projModelCR W) (hτ : τ.hom ≫ projModelStrCR W = projModelStrCR W)
    (hτpt : ∀ {X : Scheme.{0}} (t : X ⟶ base (T := T)) (x : SchemeHomOver t (projModelStrCR W)),
      x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) Q)).1) :
    (basisDivisor G q P Q).comap (pullback.lift (pullback.fst (projModelStrCR W) (𝟙 (base (T := T))) ≫ τ.hom)
        (pullback.snd (projModelStrCR W) (𝟙 (base (T := T))))
        (by rw [Category.assoc, hτ]; exact pullback.condition)) = basisDivisor G q P Q := by
  classical
  have hτ' : τ.inv ≫ projModelStrCR W = projModelStrCR W := by
    have h := congrArg (fun k => τ.inv ≫ k) hτ
    simp only [Iso.inv_hom_id_assoc] at h
    exact h.symm
  let ψ : pullback (projModelStrCR W) (𝟙 (base (T := T))) ≅ pullback (projModelStrCR W) (𝟙 (base (T := T))) :=
    { hom := pullback.lift (pullback.fst (projModelStrCR W) (𝟙 (base (T := T))) ≫ τ.hom)
        (pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) (by rw [Category.assoc, hτ]; exact pullback.condition)
      inv := pullback.lift (pullback.fst (projModelStrCR W) (𝟙 (base (T := T))) ≫ τ.inv)
        (pullback.snd (projModelStrCR W) (𝟙 (base (T := T)))) (by rw [Category.assoc, hτ']; exact pullback.condition)
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, τ.hom_inv_id,
            Category.comp_id, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, τ.inv_hom_id,
            Category.comp_id, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  haveI : IsIso ψ.hom := ⟨ψ.inv, ψ.hom_inv_id, ψ.inv_hom_id⟩
  haveI : IsOpenImmersion ψ.hom := inferInstance
  show (basisDivisor G q P Q).comap ψ.hom = basisDivisor G q P Q
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0
    simp [basisDivisor, prodKerGraph, Scheme.IdealSheafData.comap_top]

  have hQ1 : schemeHomOverComp (𝟙 (base (T := T))) (Category.comp_id _) Q = Q := Subtype.ext (Category.id_comp _)
  have hshift : ∀ a b : ℕ, b < q →
      G.mul _ (linComb G P Q a b) Q = linComb G P Q a ((b + 1) % q) := by
    intro a b hb
    show G.mul _ (G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q)) Q = G.mul _ (G.nsmul _ a P) (G.nsmul _ ((b + 1) % q) Q)
    rw [G.mul_assoc, ← RelativeGroupLaw.nsmul_succ]
    by_cases h : b + 1 < q
    · rw [Nat.mod_eq_of_lt h]
    · have hbq : b + 1 = q := by omega
      rw [hbq, Nat.mod_self, hQ, RelativeGroupLaw.nsmul_zero]

  have hgraph : ∀ a b : ℕ, b < q →
      graphOver (projModelStrCR W) (linComb G P Q a b).1 (linComb G P Q a b).2 ≫ ψ.hom =
        graphOver (projModelStrCR W) (linComb G P Q a ((b + 1) % q)).1 (linComb G P Q a ((b + 1) % q)).2 := by
    intro a b hb
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, graphOver_fst, graphOver_fst, hτpt, hQ1, hshift a b hb]
    · rw [Category.assoc, pullback.lift_snd, graphOver_snd, graphOver_snd]
  have hker : ∀ a b : ℕ, b < q →
      (graphOver (projModelStrCR W) (linComb G P Q a ((b + 1) % q)).1 (linComb G P Q a ((b + 1) % q)).2).ker.comap ψ.hom =
        (graphOver (projModelStrCR W) (linComb G P Q a b).1 (linComb G P Q a b).2).ker := by
    intro a b hb
    rw [comap_ker_hom, ← hgraph a b hb, Category.assoc, ψ.hom_inv_id, Category.comp_id]

  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let σ : Equiv.Perm (Fin ((q' + 1) * (q' + 1))) :=
    (finProdFinEquiv.symm.trans ((Equiv.refl (Fin (q' + 1))).prodCongr (finRotate (q' + 1)))).trans finProdFinEquiv
  have hσdiv : ∀ j : Fin ((q' + 1) * (q' + 1)), (σ j).val / (q' + 1) = j.val / (q' + 1) := by
    intro j
    have h := congrArg Prod.fst (finProdFinEquiv_symm_apply (σ j))
    rw [show finProdFinEquiv.symm (σ j) = (j.divNat, finRotate (q' + 1) j.modNat) from by
      simp [σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply]] at h
    have := congrArg Fin.val h
    rw [Fin.coe_divNat, Fin.coe_divNat] at this
    exact this.symm
  have hσmod : ∀ j : Fin ((q' + 1) * (q' + 1)), (σ j).val % (q' + 1) = (j.val % (q' + 1) + 1) % (q' + 1) := by
    intro j
    have h := congrArg Prod.snd (finProdFinEquiv_symm_apply (σ j))
    rw [show finProdFinEquiv.symm (σ j) = (j.divNat, finRotate (q' + 1) j.modNat) from by
      simp [σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply]] at h
    have := congrArg Fin.val h
    rw [Fin.coe_modNat, finRotate_succ_apply, Fin.val_add, Fin.val_one', Fin.coe_modNat, Nat.add_mod_mod] at this
    exact this.symm

  show (prodKerGraph (projModelStrCR W) (basisTuple G (q' + 1) P Q) (basisTuple_over G (q' + 1) P Q)).comap ψ.hom =
    prodKerGraph (projModelStrCR W) (basisTuple G (q' + 1) P Q) (basisTuple_over G (q' + 1) P Q)
  rw [prodKerGraph_eq_prod, comap_prod_of_isOpenImmersion,
    ← Equiv.prod_comp σ (fun i => ((graphOver (projModelStrCR W) (basisTuple G (q' + 1) P Q i) (basisTuple_over G (q' + 1) P Q i)).ker.comap ψ.hom))]
  refine Finset.prod_congr rfl fun j _ => ?_
  show (graphOver (projModelStrCR W) (linComb G P Q ((σ j).val / (q' + 1)) ((σ j).val % (q' + 1))).1
      (linComb G P Q ((σ j).val / (q' + 1)) ((σ j).val % (q' + 1))).2).ker.comap ψ.hom =
    (graphOver (projModelStrCR W) (linComb G P Q (j.val / (q' + 1)) (j.val % (q' + 1))).1
      (linComb G P Q (j.val / (q' + 1)) (j.val % (q' + 1))).2).ker
  rw [graphOver_ker_congr (projModelStrCR W) _ (linComb G P Q (j.val / (q' + 1)) ((j.val % (q' + 1) + 1) % (q' + 1)))
    (by rw [hσdiv, hσmod])]
  exact hker _ _ (Nat.mod_lt _ (by omega))

end S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one (solution)
