-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.admissible_over_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:56.897349+00:00
-- url     : https://prove2.me/submissions/6b4c6fb7-7d1a-49d0-a4c8-4ad4cd35cc07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_ratio_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_exists_val_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_indep_u
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_val_eval_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_nonneg_of_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_residueTrdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
open ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.PlOver la c) :
    d.admitted c (d.Wres c w) ∧ IsOver (K := K) (d.Wres c w) la ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0 := by
  classical
  obtain ⟨hNZ, hpl⟩ := hw

  have hex : ∀ j, ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    intro j
    have hb := hd.w_base c
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL)
      (fun h0 => hb (congrArg Subtype.val h0))).mp (hd.finrank_one c d.wL) ⟨d.w j c, hd.w_mem j c⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  let a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)
  have ha : ∀ j, d.w j c = a j • d.w (d.jc c) c := fun j => by
    obtain ⟨b, hb⟩ := hex j
    rw [show a j = b from ratio_eq (hd.w_base c) hb]
    exact hb
  have ha_jc : a (d.jc c) = 1 := ratio_eq (hd.w_base c) (one_smul _ _).symm
  let f := algebraMap (Ω c) (OmS (Ω c) d.D d.N)
  obtain ⟨j0, -, hj0⟩ := Finset.univ.exists_min_image (fun j => w (f (a j))) Finset.univ_nonempty
  have hj0' : ∀ j, w (f (a j0)) ≤ w (f (a j)) := fun j => hj0 j (Finset.mem_univ _)
  have ha0 : a j0 ≠ 0 := by
    intro h0
    have := hj0' (d.jc c)
    rw [h0, ha_jc, map_zero, map_one, AddValuation.map_zero, AddValuation.map_one] at this
    exact absurd (top_le_iff.mp this) WithTop.zero_ne_top
  have hf0 : f (a j0) ≠ 0 := (map_ne_zero f).mpr ha0
  have hw0 : d.w j0 c ≠ 0 := by rw [ha j0]; exact smul_ne_zero ha0 (hd.w_base c)
  let r : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)
  have hr : ∀ j, r j * a j0 = a j := fun j => by
    have : r j = a j / a j0 :=
      ratio_eq hw0 (by rw [ha j, ha j0, smul_smul, div_mul_cancel₀ _ ha0])
    rw [this, div_mul_cancel₀ _ ha0]
  have hr0 : r j0 = 1 := ratio_eq hw0 (one_smul _ _).symm
  have hrint : ∀ j, 0 ≤ w (f (r j)) := fun j => by
    have e : w (f (r j)) + w (f (a j0)) = w (f (a j)) := by
      rw [← AddValuation.map_mul, ← map_mul, hr]
    exact wt_nonneg_of_add (hNZ.1 _ hf0) e (hj0' j)

  let s : TVar d.D d.N → OmS (Ω c) d.D d.N := sImg (D := d.D) (d.jc c) (d.x c)
  have hOT : ∀ p, d.OTtoS c (MvPolynomial.X p) = s p := by
    intro p; simp [Data.OTtoS, OTtoKT, Data.sH, sHom, s]
  have hX0 : ∀ p, 0 ≤ w (s p) := fun p => by rw [← hOT]; exact (hpl _).1
  have hC : ∀ y : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (MvPolynomial.C y) = f y := fun y =>
    (IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) _ y).symm
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 → ∑ j, s (i, j) * f (a j) = 0 := by
    intro i hi
    rw [Fin.sum_univ_succAbove _ (d.jc c)]
    simp only [s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, hi, ↓reduceIte, ha_jc, map_one, mul_one, map_neg, map_sum,
      map_mul, hC]
    rw [neg_add_eq_zero]
    rfl
  have hrel0 : ∀ i : Fin (d.D + 1), i ≠ 0 →
      s (i, j0) = -∑ k, s (i, j0.succAbove k) * f (r (j0.succAbove k)) := by
    intro i hi
    have h1 := hrel i hi
    have e : ∀ j, s (i, j) * f (a j) = (s (i, j) * f (r j)) * f (a j0) := fun j => by
      rw [← hr j, map_mul, mul_assoc]
    simp only [e, ← Finset.sum_mul] at h1
    have h2 := (mul_eq_zero.mp h1).resolve_right hf0
    rw [Fin.sum_univ_succAbove _ j0, hr0, map_one, mul_one] at h2
    exact eq_neg_of_add_eq_zero_left h2

  let q0 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), j0)) (fun ik => (ik.1, j0.succAbove ik.2))
  let t : SVar d.D d.N → OmS (Ω c) d.D d.N := fun x => s (q0 x)
  have ht : ∀ x, t x ∈ vRing w := fun x => hX0 _
  let p : TVar d.D d.N → MvPolynomial (SVar d.D d.N) (Ω c) := fun ij =>
    Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) j0
      (if ij.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (ij.1, k)) * MvPolynomial.C (r (j0.succAbove k)))
      (fun k => MvPolynomial.X (Sum.inr (ij.1, k))) ij.2
  have hpj0 : ∀ i, p (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (r (j0.succAbove k)) := by
    intro i; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
  have hpk : ∀ i k, p (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
    intro i k; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hpu : ∀ ij, MvPolynomial.aeval t (p ij) = s ij := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs with hi
      · subst hi; simp [t, q0]
      · rw [hrel0 i hi]; simp [t, q0]; rfl
    · rw [hpk]; simp [t, q0]

  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) f
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap f) (algebraMap K (Ω c))
  let k₁ : IntermediateField (ResidueField (((vRing w).comap f).comap (algebraMap K (Ω c))))
      (ResidueField ((vRing w).comap f)) :=
    IntermediateField.adjoin _ {z | ∃ j, ∃ h : r j ∈ (vRing w).comap f,
      z = residue ((vRing w).comap f) ⟨r j, h⟩}
  let R3 : Subring (MvPolynomial (SVar d.D d.N) (Ω c)) :=
    ((MvPolynomial.map (algebraMap k₁ (ResidueField ((vRing w).comap f)))).range.comap
      (MvPolynomial.map (residue ((vRing w).comap f)))).map
        (MvPolynomial.map ((vRing w).comap f).subtype)
  have hR3X : ∀ x, (MvPolynomial.X x : MvPolynomial (SVar d.D d.N) (Ω c)) ∈ R3 := fun x =>
    ⟨MvPolynomial.X x, ⟨MvPolynomial.X x, by simp⟩, by simp⟩
  have hR3C : ∀ j, MvPolynomial.C (r j) ∈ R3 := fun j =>
    ⟨MvPolynomial.C ⟨r j, hrint j⟩,
      ⟨MvPolynomial.C ⟨_, IntermediateField.subset_adjoin _ _ ⟨j, hrint j, rfl⟩⟩, by simp⟩, by simp⟩
  have hpR3 : ∀ ij, p ij ∈ R3 := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs
      · exact hR3X _
      · exact R3.neg_mem (R3.sum_mem fun k _ => R3.mul_mem (hR3X _) (hR3C _))
    · rw [hpk]; exact hR3X _
  have hcoefW : ∀ P ∈ R3, ∀ α, P.coeff α ∈ (vRing w).comap f := by
    intro P hP α
    obtain ⟨Q, -, rfl⟩ := hP
    rw [MvPolynomial.coeff_map]
    exact (Q.coeff α).2
  have hcoefk : ∀ P ∈ R3, ∀ α (hα : P.coeff α ∈ (vRing w).comap f),
      residue ((vRing w).comap f) ⟨_, hα⟩ ∈ k₁ := by
    intro P hP α hα
    obtain ⟨Q, ⟨Z, hZ⟩, rfl⟩ := hP
    have e : (⟨_, hα⟩ : (vRing w).comap f) = Q.coeff α := Subtype.ext (MvPolynomial.coeff_map _ _ _)
    rw [e]
    have := congrArg (MvPolynomial.coeff α) hZ
    simp only [MvPolynomial.coeff_map] at this
    rw [← this]
    exact (Z.coeff α).2
  have hp : ∀ ij α, (p ij).coeff α ∈ (vRing w).comap f := fun ij α => hcoefW _ (hpR3 ij) α

  let u : TVar d.D d.N → vRing w := fun ij => ⟨s ij, hX0 ij⟩
  have hKU : algebraMap K (OmS (Ω c) d.D d.N) = f.comp (algebraMap K (Ω c)) :=
    RingHom.ext fun x => IsScalarTower.algebraMap_apply K (Ω c) _ x
  have hOT' : ∀ P, d.OTtoS c P =
      MvPolynomial.eval₂ (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) s P := by
    intro P
    simp only [Data.OTtoS, OTtoKT, Data.sH, sHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hKU]
    rfl
  have hCla : ∀ x : 𝓞 K, (∀ m, (MvPolynomial.C x : OT K d.D d.N).coeff m ∈ la.asIdeal) ↔
      x ∈ la.asIdeal := by
    intro x
    constructor
    · intro h0; simpa using h0 0
    · intro h0 m; rw [MvPolynomial.coeff_C]; split_ifs <;> simp [h0]
  have h0 : ∀ P : MvPolynomial (TVar d.D d.N) (𝓞 K), 0 < w (MvPolynomial.eval₂
      (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) (fun j => (u j : OmS (Ω c) d.D d.N)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal := by
    intro P
    show 0 < w (MvPolynomial.eval₂ _ s P) ↔ _
    rw [← hOT' P, (hpl P).2, laT, MvPolynomial.mem_map_C_iff]
  have h1 : ∀ x : 𝓞 K, 0 ≤ w ((f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) x) := by
    intro x
    have := (hpl (MvPolynomial.C x)).1
    rwa [hOT', MvPolynomial.eval₂_C] at this
  have hind_u := indep_u (Ω := Ω c) w la u h0 h1
  have hcard : Fintype.card (TVar d.D d.N) = Fintype.card (SVar d.D d.N) + d.D := by
    simp [Fintype.card_sum, Fintype.card_prod]; ring
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K (Ω c) (OmS (Ω c) d.D d.N) d.D (hd.trdeg c)
    (SVar d.D d.N) t (vRing w) ht (TVar d.D d.N) u p hp hcard hpu hind_u
  have htrk : Algebra.trdeg _ k₁ = d.D := RT.1 k₁ (fun j α => hcoefk _ (hpR3 j) α (hp j α))
  have hG := RT.2.2

  let q1 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), d.jc c)) (fun ik => (ik.1, (d.jc c).succAbove ik.2))
  have hψ : ∀ P : MvPolynomial (SVar d.D d.N) (Ω c),
      MvPolynomial.aeval t (MvPolynomial.aeval (fun x => p (q1 x)) P) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P := by
    have e : (MvPolynomial.aeval t).comp (MvPolynomial.aeval (fun x => p (q1 x))) =
        IsScalarTower.toAlgHom (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', hpu]
      rcases x with _ | ⟨i, k⟩
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
    intro P
    exact DFunLike.congr_fun e P
  have hNorm : IsNormDiscrete (d.Wres c w) := by
    refine ⟨fun x hx => hNZ.1 _ ((map_ne_zero f).mpr hx), ?_⟩
    obtain ⟨π', hπ'⟩ := hNZ.2
    obtain ⟨P, Q, hQ, hPQ⟩ :=
      IsFractionRing.div_surjective (A := MvPolynomial (SVar d.D d.N) (Ω c)) π'
    have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
    have hinj := IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
    have hP0 : P ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hPQ
      rw [← hPQ, AddValuation.map_zero] at hπ'
      exact absurd hπ' (by simp)
    have hne : ∀ R : MvPolynomial (SVar d.D d.N) (Ω c), R ≠ 0 →
        MvPolynomial.aeval (fun x => p (q1 x)) R ≠ 0 := by
      intro R hR h0'
      apply hR; apply hinj
      rw [← hψ, h0', map_zero, map_zero]
    obtain ⟨c1, -, e1⟩ := exists_val_coeff w t ht hG _ (hne P hP0)
    obtain ⟨c2, hc2, e2⟩ := exists_val_coeff w t ht hG _ (hne Q hQ0)
    rw [hψ] at e1 e2
    refine ⟨c1 / c2, ?_⟩
    have hQU : algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) Q ≠ 0 :=
      fun h0' => hQ0 (hinj (h0'.trans (map_zero _).symm))
    have k1 : w π' + w (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) Q) =
        w (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P) := by
      rw [← AddValuation.map_mul, ← hPQ, div_mul_cancel₀ _ hQU]
    have k2 : w (f (c1 / c2)) + w (f c2) = w (f c1) := by
      rw [← AddValuation.map_mul, ← map_mul, div_mul_cancel₀ _ hc2]
    rw [hπ', e1, e2] at k1
    show w (f (c1 / c2)) = 1
    exact wt_cancel (hNZ.1 _ ((map_ne_zero f).mpr hc2)) (k2.trans k1.symm)
  have hOver : IsOver (K := K) (d.Wres c w) la := by
    intro x
    have := hpl (MvPolynomial.C x)
    rw [hOT', MvPolynomial.eval₂_C] at this
    show 0 < w ((f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) x) ↔ _
    rw [this.2, laT, MvPolynomial.mem_map_C_iff]
    exact hCla x
  refine ⟨⟨hNorm, Or.inl ⟨la, hOver, RT.2.1, j0, hw0, hrint, htrk⟩⟩, hOver, j0, hw0, hrint, ?_⟩

  have hsH : ∀ q, d.sH c (MvPolynomial.X q) = s q := fun q => by simp [Data.sH, sHom, s]
  have hsum : (∑ j, d.sH c (MvPolynomial.X (0, j)) * f (r j)) =
      MvPolynomial.aeval t (∑ j, p (0, j) * MvPolynomial.C (r j)) := by
    simp only [map_sum, map_mul, hpu, MvPolynomial.aeval_C, hsH]
    rfl
  show w (∑ j, d.sH c (MvPolynomial.X (0, j)) * f (r j)) = 0
  rw [hsum]
  have hL : (∑ j, p (0, j) * MvPolynomial.C (r j)) ∈ R3 :=
    R3.sum_mem fun j _ => R3.mul_mem (hpR3 _) (hR3C _)
  refine val_eval_eq_zero w t ht hG _ (fun β => hcoefW _ hL β) (Finsupp.single (Sum.inl ()) 1) ?_
  rw [MvPolynomial.coeff_sum, Fin.sum_univ_succAbove _ j0]
  simp only [hpj0, hpk, ↓reduceIte, hr0, map_one, mul_one]
  rw [MvPolynomial.coeff_X', if_pos rfl, Finset.sum_eq_zero, add_zero]
  intro x _
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', if_neg, mul_zero]
  rw [Finsupp.single_left_inj one_ne_zero]
  simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
