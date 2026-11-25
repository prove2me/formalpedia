-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.PlaceTrivialOrPositive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:18.469285+00:00
-- url     : https://prove2.me/submissions/4d2efec1-e02a-47a9-8d70-e51139057343

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_uniformizer_of_residue_indep
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_integral_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_genericHomAt_relation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_val_algebraMap_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algebraicIndependent_residue_of_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_card_baseOrOffColumn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_rename_notMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_genericImage_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_genericImage_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_valuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scalarRatio_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trdeg_eq_of_card
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trdeg_residue_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N))
    (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) :
    (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) := by
  classical
  by_cases htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0
  · exact Or.inl htriv
  right
  simp only [not_forall] at htriv
  obtain ⟨a0, ha0, hva0⟩ := htriv
  have hvK : IsTrivOn K (d.Wres c w) := by
    intro a ha
    show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a)) = 0
    rw [← IsScalarTower.algebraMap_apply]
    exact d.val_algebraMap_eq_zero c p w hw a ha
  obtain ⟨j0, hw0, hint, hx0, hq⟩ := d.exists_integral_base hd c (d.Wres c w)
  have htr := trdeg_residue_le d.D (hd.trdeg c) (d.Wres c w) hvK a0 ha0 hva0
  letI iWV : Algebra (IsLocalRing.ResidueField (vRing (d.Wres c w)))
      (IsLocalRing.ResidueField (vRing w)) := resAlg (F := Ω c) w
  letI iRW := resAlg (F := K) (d.Wres c w)
  letI iRV : Algebra (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
        (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let t' : TVar d.D d.N → vRing w := fun e => ⟨d.sH c (X e), (hw.2 (X e)).1⟩
  let ρ : Fin (d.N + 1) → IsLocalRing.ResidueField (vRing (d.Wres c w)) := fun j =>
    IsLocalRing.residue _ ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩
  have hres : ∀ i, i ≠ 0 → IsLocalRing.residue (vRing w) (t' (i, j0)) =
      -∑ j ∈ Finset.univ.erase j0, IsLocalRing.residue (vRing w) (t' (i, j)) *
        algebraMap _ (IsLocalRing.ResidueField (vRing w)) (ρ j) := by
    intro i hi
    have hV : t' (i, j0) = -∑ j ∈ Finset.univ.erase j0, t' (i, j) *
        comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩ := by
      apply Subtype.ext
      push_cast
      exact d.genericHomAt_relation hd c j0 hw0 hq i hi
    rw [hV, map_neg, map_sum]
    congr 1
  obtain ⟨e0, he0⟩ := exists_rename_notMem p hp
  have hcK : ∀ a : K, algebraMap K (OmS (Ω c) d.D d.N) a ∈ vRing w := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    · rw [mem_valuationRing, d.val_algebraMap_eq_zero c p w hw a ha]
  have hoK : ∀ a : K, a ∈ (vRing (d.Wres c w)).comap (algebraMap K (Ω c)) := by
    intro a
    show algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a) ∈ vRing w
    rw [← IsScalarTower.algebraMap_apply]
    exact hcK a
  let φ : K →+* vRing w := (algebraMap K (OmS (Ω c) d.D d.N)).codRestrict (vRing w) hcK
  let ψ : K →+* IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))) :=
    (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict _ hoK)
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨x.1, rfl⟩
  have hc : ∀ a, algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) (ψ a) = IsLocalRing.residue (vRing w) (φ a) := by
    intro a
    show IsLocalRing.residue (vRing w) (comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
      (comapIncl (vRing (d.Wres c w)) (algebraMap K (Ω c)) ⟨a, hoK a⟩)) = _
    exact congrArg _ (Subtype.ext (IsScalarTower.algebraMap_apply K (Ω c) _ a).symm)
  have hu : AlgebraicIndependent (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (fun e : {e // e ≠ e0} => IsLocalRing.residue (vRing w) (t' e.1)) := by
    apply algebraicIndependent_residue_of_isUnit (vRing w) φ ψ hψ hc (fun e : {e // e ≠ e0} => t' e.1)
    intro q hq
    have hq0 : q ≠ 0 := by rintro rfl; exact hq (map_zero _)
    have hnot := he0 q hq0
    have hcoe : ((eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q : vRing w) : OmS (Ω c) d.D d.N) =
        d.sH c (rename Subtype.val q) := by
      have e1 := eval₂_comp_left (vRing w).subtype φ (fun e : {e // e ≠ e0} => t' e.1) q
      have e2 : (vRing w).subtype.comp φ = algebraMap K (OmS (Ω c) d.D d.N) := RingHom.ext fun _ => rfl
      rw [e2] at e1
      refine e1.trans ?_
      conv_rhs => rw [MvPolynomial.aeval_unique (d.sH c), aeval_rename, aeval_def]
      rfl
    have h0 := (hw.2 (rename Subtype.val q)).1
    have h1 : ¬ (0 < w (d.sH c (rename Subtype.val q))) := fun h => hnot ((hw.2 _).2.mp h)
    have hv0 : w (d.sH c (rename Subtype.val q)) = 0 := le_antisymm (not_lt.mp h1) h0
    have he : eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q = ⟨d.sH c (rename Subtype.val q), h0⟩ :=
      Subtype.ext hcoe
    rw [he]
    exact isUnit_of_val_eq_zero' w h0 hv0
  let tb : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} → IsLocalRing.ResidueField (vRing w) :=
    fun e => IsLocalRing.residue (vRing w) (t' e.1)
  have hmemG : ∀ (M : Type) [Field M] [Algebra M (IsLocalRing.ResidueField (vRing w))],
      (∀ j, ∃ m : M, algebraMap M (IsLocalRing.ResidueField (vRing w)) m =
        algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j)) →
      ∀ e : {e // e ≠ e0}, IsLocalRing.residue (vRing w) (t' e.1) ∈ Algebra.adjoin M (Set.range tb) := by
    intro M _ _ hM e
    obtain ⟨⟨i, j⟩, he⟩ := e
    by_cases hij : i = 0 ∨ j ≠ j0
    · exact Algebra.subset_adjoin ⟨⟨(i, j), hij⟩, rfl⟩
    · rw [not_or, not_not] at hij
      obtain ⟨hi, rfl⟩ := hij
      show IsLocalRing.residue (vRing w) (t' (i, _)) ∈ _
      rw [hres i hi]
      refine neg_mem (Subalgebra.sum_mem _ fun j hj => Subalgebra.mul_mem _ ?_ ?_)
      · exact Algebra.subset_adjoin ⟨⟨(i, j), Or.inr (Finset.ne_of_mem_erase hj)⟩, rfl⟩
      · obtain ⟨m, hm⟩ := hM j
        rw [← hm]
        exact Subalgebra.algebraMap_mem _ m
  have hcard : Fintype.card {e : TVar d.D d.N // e ≠ e0} =
      Fintype.card {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} + (d.D - 1) := by
    rw [card_subtype_ne', card_baseOrOffColumn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h3 := hd.D_ge
    have h4 : d.D + 1 ≤ (d.D + 1) * (d.N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  obtain ⟨htrW, hindW⟩ := trdeg_eq_of_card tb _ hu (hmemG _ fun j => ⟨ρ j, rfl⟩) (d.D - 1) htr hcard (fun _ => rfl)
  let k1 := IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
    {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing (d.Wres c w),
      r = IsLocalRing.residue (vRing (d.Wres c w)) ⟨_, h⟩}
  letI ik1 : Algebra k1 (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap k1 (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  have hk1le := (trdeg_le_of_injective k1.val Subtype.val_injective).trans htr
  obtain ⟨htrk1, -⟩ := trdeg_eq_of_card (E := k1) tb _ hu
    (hmemG k1 fun j => ⟨⟨ρ j, IntermediateField.subset_adjoin _ _ ⟨j, hint j, rfl⟩⟩, rfl⟩) (d.D - 1) hk1le hcard (fun _ => rfl)
  have hRC : d.ResCond c (d.Wres c w) (d.D - 1) := ⟨htrW, j0, hw0, fun j => hint j, htrk1⟩

  have hz0mem : (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∈ vRing w :=
    sum_mem fun j _ => mul_mem (hw.2 (X (0, j))).1 (hint j)
  have hz0V : (⟨_, hz0mem⟩ : vRing w) = ∑ j, t' (0, j) *
      comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ⟨_, hint j⟩ := by
    apply Subtype.ext
    push_cast
    rfl
  have hres0 : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ =
      ∑ j, algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j) *
        tb ⟨(0, j), Or.inl rfl⟩ := by
    rw [hz0V, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_comm]
    rfl
  have hli := hindW.linearIndependent.comp
    (fun j : Fin (d.N + 1) => (⟨(0, j), Or.inl rfl⟩ : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0}))
    (fun a b hab => by simpa using hab)
  have hρ0 : ρ j0 = 1 := by
    have e : (⟨ratio (Ω := Ω c) (d.w j0 c) (d.w j0 c), hint j0⟩ : vRing (d.Wres c w)) = 1 :=
      Subtype.ext (scalarRatio_eq hw0 (one_smul _ _).symm)
    show IsLocalRing.residue _ _ = 1
    rw [e, map_one]
  have hne : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.mp hli ρ (by
      rw [← h0, hres0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def]
      rfl) j0
    rw [hρ0] at this
    exact one_ne_zero this
  have hunit : w (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0 :=
    val_eq_zero_of_isUnit' w hz0mem ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)

  have hNorm : IsNormDiscrete (d.Wres c w) := by
    refine ⟨fun x hx => hw.1.1 _ ((map_ne_zero _).mpr hx), ?_⟩
    let G : TVar d.D d.N → MvPolynomial {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} (Ω c) := fun e =>
      if h : e.1 = 0 ∨ e.2 ≠ j0 then X ⟨e, h⟩ else
        -∑ j ∈ (Finset.univ.erase j0).attach,
          X ⟨(e.1, j.1), Or.inr (Finset.ne_of_mem_erase j.2)⟩ *
            C (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))
    have hG : ∀ e, d.sH c (X e) =
        aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (G e) := by
      rintro ⟨i, j⟩
      by_cases h : i = 0 ∨ j ≠ j0
      · simp only [G, dif_pos h, aeval_X]
      · simp only [G, dif_neg h, map_neg, map_sum, map_mul, aeval_X, aeval_C]
        rw [not_or, not_not] at h
        obtain ⟨hi, hj⟩ := h
        subst j
        rw [d.genericHomAt_relation hd c _ hw0 hq i hi]
        congr 1
        exact (Finset.sum_attach _ (fun j => d.sH c (X (i, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))).symm
    have hg : ∀ x : SVar d.D d.N,
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (X x) =
          aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
            (Sum.elim (fun _ => G (0, d.jc c)) (fun ik => G (ik.1, (d.jc c).succAbove ik.2)) x) := by
      rintro (_ | ⟨i, k⟩)
      · rw [Sum.elim_inl, ← hG]
        simp [Data.sH, sHom, genericImage_base]
      · rw [Sum.elim_inr, ← hG]
        simp [Data.sH, sHom, genericImage_succAbove]
    obtain ⟨π, hπ⟩ := uniformizer_of_residue_indep w hw.1
      (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
      (fun e => (hw.2 (X e.1)).1) hindW _ hg
    exact ⟨π, hπ⟩
  exact ⟨⟨hNorm, Or.inr ⟨hvK, hRC⟩⟩, hvK, j0, hw0, fun j => hint j, hunit⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data
