-- Prove2me | solution 1 for PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3916ccb6-eda3-5455-916b-0eac00071f68

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_exists_forall_exists_polynomial_aeval_eq_of_norm_le_one
import Theorems.Thm_PadicAlgCl_norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower
import Theorems.Thm_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
import Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped Classical

namespace TTA

open Polynomial IntermediateField

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "Q" => PadicAlgCl.cyclotomicTower p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma norm_algEquiv (σ : Γ) (x : Ω) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

lemma norm_algEquiv_sub (σ : Γ) (x y : Ω) : ‖σ x - σ y‖ = ‖x - y‖ := by
  rw [← map_sub, norm_algEquiv]

lemma exists_norm_pow_mul_le_one (z : Ω) : ∃ k : ℕ, ‖(p : Ω) ^ k * z‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ (one_lt_p p)
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, norm_natCast_p, inv_pow]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (p_pos p) k
  calc ((p : ℝ) ^ k)⁻¹ * ‖z‖ ≤ ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k := by gcongr
    _ = 1 := inv_mul_cancel₀ hpk.ne'

def IntPoly (P : ℚ_[p][X]) : Prop := ∀ i, ‖P.coeff i‖ ≤ 1

lemma norm_pow_sub_pow_le {u w : Ω} (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖u ^ k - w ^ k‖ ≤ ‖u - w‖ := by
  have h := (Commute.all u w).geom_sum₂_mul k
  rw [← h, norm_mul]
  have hs : ‖∑ i ∈ Finset.range k, u ^ i * w ^ (k - 1 - i)‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hu) (by positivity)
      (pow_le_one₀ (norm_nonneg _) hw)
  calc ‖∑ i ∈ Finset.range k, u ^ i * w ^ (k - 1 - i)‖ * ‖u - w‖ ≤ 1 * ‖u - w‖ := by gcongr
    _ = ‖u - w‖ := one_mul _

lemma norm_aeval_le_one {P : ℚ_[p][X]} (hP : IntPoly p P) {u : Ω} (hu : ‖u‖ ≤ 1) :
    ‖aeval u P‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro i _
  rw [Algebra.smul_def, norm_mul, norm_pow, norm_algebraMap']
  exact mul_le_one₀ (hP i) (by positivity) (pow_le_one₀ (norm_nonneg _) hu)

lemma norm_aeval_sub_aeval_le {P : ℚ_[p][X]} (hP : IntPoly p P) {u w : Ω} (hu : ‖u‖ ≤ 1)
    (hw : ‖w‖ ≤ 1) : ‖aeval u P - aeval w P‖ ≤ ‖u - w‖ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
  intro i _
  rw [← smul_sub, Algebra.smul_def, norm_mul, norm_algebraMap']
  calc ‖P.coeff i‖ * ‖u ^ i - w ^ i‖ ≤ 1 * ‖u - w‖ :=
        mul_le_mul (hP i) (norm_pow_sub_pow_le p hu hw i) (norm_nonneg _) zero_le_one
    _ = ‖u - w‖ := one_mul _

lemma prod_le_prod_of_subset {ι : Type*} {s t : Finset ι} (h : s ⊆ t) {f : ι → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  rw [← Finset.prod_sdiff h]
  have hA : ∏ i ∈ t \ s, f i ≤ 1 :=
    Finset.prod_le_one (fun i hi => h0 i (Finset.sdiff_subset hi))
      (fun i hi => h1 i (Finset.sdiff_subset hi))
  have hB : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => h0 i (h hi)
  calc (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i ≤ 1 * ∏ i ∈ s, f i := by gcongr
    _ = ∏ i ∈ s, f i := one_mul _

lemma prod_max_le_max_prod {ι : Type*} (s : Finset ι) {f : ι → ℝ} {r : ℝ}
    (_h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∏ i ∈ s, max (f i) r ≤ max (∏ i ∈ s, f i) r := by
  by_cases hall : ∀ i ∈ s, r ≤ f i
  · rw [Finset.prod_congr rfl fun i hi => max_eq_left (hall i hi)]
    exact le_max_left _ _
  · push Not at hall
    obtain ⟨i₀, hi₀, hlt⟩ := hall
    rw [← Finset.mul_prod_erase s _ hi₀, max_eq_right hlt.le]
    have hrest : ∏ i ∈ s.erase i₀, max (f i) r ≤ 1 :=
      Finset.prod_le_one (fun i _ => le_max_of_le_right hr0)
        (fun i hi => max_le (h1 i (Finset.mem_of_mem_erase hi)) hr1)
    calc r * ∏ i ∈ s.erase i₀, max (f i) r ≤ r * 1 := by gcongr
      _ = r := mul_one r
      _ ≤ max (∏ i ∈ s, f i) r := le_max_right _ _

lemma max_pow_le (a b : ℝ) (m : ℕ) :
    (max a b) ^ m ≤ max (a ^ m) (b ^ m) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact le_max_left _ _

section LevelField

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isGalois_of_normal [Normal ℚ_[p] L] : IsGalois ℚ_[p] L := IsGalois.mk

lemma norm_sub_le_max (a b : Ω) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

private def _root_.TTA.lift (g : L ≃ₐ[ℚ_[p]] L) : Γ := AlgEquiv.liftNormal g (PadicAlgCl p)

p2m_export "TTA" "lift"
lemma lift_coe (g : L ≃ₐ[ℚ_[p]] L) (z : L) : lift p L g z = g z :=
  AlgEquiv.liftNormal_commutes g (PadicAlgCl p) z

def res [Normal ℚ_[p] L] (σ : Γ) : L ≃ₐ[ℚ_[p]] L := σ.restrictNormal L

lemma coe_res [Normal ℚ_[p] L] (σ : Γ) (z : L) : ((res p L σ z : L) : Ω) = σ z :=
  AlgEquiv.restrictNormal_commutes σ L z

lemma norm_coe_apply (g : L ≃ₐ[ℚ_[p]] L) (z : L) : ‖((g z : L) : Ω)‖ = ‖(z : Ω)‖ := by
  rw [← lift_coe, norm_algEquiv]

lemma norm_coe_apply_sub (g : L ≃ₐ[ℚ_[p]] L) (z w : L) :
    ‖((g z : L) : Ω) - g w‖ = ‖(z : Ω) - w‖ := by
  rw [← lift_coe, ← lift_coe, norm_algEquiv_sub]

lemma coe_aeval (z : L) (P : ℚ_[p][X]) : ((aeval z P : L) : Ω) = aeval (z : Ω) P := by
  have h := aeval_algHom_apply L.val z P
  rw [IntermediateField.coe_val] at h
  exact h.symm

def IntL (P : L[X]) : Prop := ∀ i, ‖((P.coeff i : L) : Ω)‖ ≤ 1

lemma norm_eval_le {P : L[X]} {C : ℝ} (hC : 0 ≤ C) (hP : ∀ i, ‖((P.coeff i : L) : Ω)‖ ≤ C)
    {u : L} (hu : ‖(u : Ω)‖ ≤ 1) : ‖((P.eval u : L) : Ω)‖ ≤ C := by
  rw [eval_eq_sum_range, AddSubmonoidClass.coe_finsetSum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro i _
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
  calc ‖((P.coeff i : L) : Ω)‖ * ‖(u : Ω)‖ ^ i ≤ C * 1 :=
        mul_le_mul (hP i) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hC
    _ = C := mul_one C

lemma intL_mul {P R : L[X]} (hP : IntL p L P) (hR : IntL p L R) : IntL p L (P * R) := by
  intro i
  rw [coeff_mul, AddSubmonoidClass.coe_finsetSum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro ij _
  rw [MulMemClass.coe_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (hR _)

lemma intL_sub {P R : L[X]} (hP : IntL p L P) (hR : IntL p L R) : IntL p L (P - R) := by
  intro i
  rw [coeff_sub, AddSubgroupClass.coe_sub]
  exact (norm_sub_le_max p _ _).trans (max_le (hP i) (hR i))

lemma intL_one : IntL p L 1 := by
  intro i
  rw [coeff_one]
  split_ifs <;> simp

lemma intL_X_sub_C {c : L} (hc : ‖(c : Ω)‖ ≤ 1) : IntL p L (X - C c) := by
  intro i
  rw [coeff_sub, coeff_X, coeff_C]
  rcases i with _ | _ | i <;> simp [hc]

lemma intL_prod {ι : Type*} (s : Finset ι) {f : ι → L[X]} (hf : ∀ i ∈ s, IntL p L (f i)) :
    IntL p L (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intL_one p L
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact intL_mul p L (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma intL_map {P : L[X]} (hP : IntL p L P) (g : L ≃ₐ[ℚ_[p]] L) :
    IntL p L (P.map (g : L →+* L)) := by
  intro i
  rw [coeff_map]
  change ‖((g (P.coeff i) : L) : Ω)‖ ≤ 1
  rw [norm_coe_apply]
  exact hP i

lemma intL_map_algebraMap {P : ℚ_[p][X]} (hP : IntPoly p P) :
    IntL p L (P.map (algebraMap ℚ_[p] L)) := by
  intro i
  rw [coeff_map]
  change ‖algebraMap ℚ_[p] Ω (P.coeff i)‖ ≤ 1
  rw [norm_algebraMap']
  exact hP i

def OL : Subring L where
  carrier := {z | ‖(z : Ω)‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    change ‖((a * b : L) : Ω)‖ ≤ 1
    rw [MulMemClass.coe_mul, norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by change ‖((1 : L) : Ω)‖ ≤ 1; simp
  add_mem' {a b} ha hb := by
    change ‖((a + b : L) : Ω)‖ ≤ 1
    rw [AddMemClass.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by change ‖((0 : L) : Ω)‖ ≤ 1; simp
  neg_mem' {a} ha := by
    change ‖((-a : L) : Ω)‖ ≤ 1
    rw [NegMemClass.coe_neg, norm_neg]
    exact ha

lemma intL_iff_mem_lifts (P : L[X]) : IntL p L P ↔ P ∈ Polynomial.lifts (OL p L).subtype := by
  rw [lifts_iff_coeff_lifts]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    exact ⟨⟨P.coeff i, h⟩, rfl⟩
  · rintro ⟨c, hc⟩
    rw [← hc]
    exact c.2

lemma intL_divByMonic {F P : L[X]} (hF : IntL p L F) (hP : IntL p L P) (hPm : P.Monic) :
    IntL p L (F /ₘ P) := by
  obtain ⟨P₀, hP₀, -, hP₀m⟩ :=
    lifts_and_natDegree_eq_and_monic ((intL_iff_mem_lifts p L P).mp hP) hPm
  obtain ⟨F₀, hF₀⟩ := (mem_lifts F).mp ((intL_iff_mem_lifts p L F).mp hF)
  rw [intL_iff_mem_lifts, mem_lifts]
  exact ⟨F₀ /ₘ P₀, by rw [map_divByMonic _ hP₀m, hF₀, hP₀]⟩

structure IsGen (x : L) : Prop where
  norm_le : ‖(x : Ω)‖ ≤ 1
  gen : ∀ z : L, ‖(z : Ω)‖ ≤ 1 → ∃ P : ℚ_[p][X], IntPoly p P ∧ aeval x P = z

lemma exists_isGen [FiniteDimensional ℚ_[p] L] : ∃ x : L, IsGen p L x := by
  obtain ⟨x₀, hx₀, -, hgen⟩ :=
    PadicAlgCl.exists_forall_exists_polynomial_aeval_eq_of_norm_le_one p L
      (⊥ : IntermediateField L (PadicAlgCl p))
  have hmem : ∀ w : (⊥ : IntermediateField L (PadicAlgCl p)), (w : Ω) ∈ L := by
    intro w
    obtain ⟨e, he⟩ := IntermediateField.mem_bot.mp w.2
    rw [← he]
    exact e.2
  refine ⟨⟨x₀, hmem x₀⟩, hx₀, fun z hz => ?_⟩
  set w : (⊥ : IntermediateField L (PadicAlgCl p)) :=
    ⟨(z : Ω), IntermediateField.mem_bot.mpr ⟨z, rfl⟩⟩ with hw
  obtain ⟨P, hP, hPw⟩ := hgen w hz
  refine ⟨P, hP, Subtype.ext ?_⟩
  rw [coe_aeval]
  have h := aeval_algHom_apply
    ((⊥ : IntermediateField L (PadicAlgCl p)).val.restrictScalars ℚ_[p]) x₀ P
  rw [hPw] at h
  exact h

variable {L}

def D (x : L) (g : L ≃ₐ[ℚ_[p]] L) : ℝ := ‖((g x : L) : Ω) - x‖

lemma D_nonneg (x : L) (g : L ≃ₐ[ℚ_[p]] L) : 0 ≤ D p x g := norm_nonneg _

lemma D_le_one {x : L} (hx : IsGen p L x) (g : L ≃ₐ[ℚ_[p]] L) : D p x g ≤ 1 := by
  unfold D
  refine (norm_sub_le_max p _ _).trans (max_le ?_ hx.norm_le)
  rw [norm_coe_apply]; exact hx.norm_le

lemma D_one (x : L) : D p x 1 = 0 := by simp [D]

lemma D_mul_le (x : L) (g h : L ≃ₐ[ℚ_[p]] L) : D p x (g * h) ≤ max (D p x g) (D p x h) := by
  unfold D
  have hsplit : ((((g * h) x : L)) : Ω) - x = (((g (h x) : L) : Ω) - g x) + (((g x : L) : Ω) - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [hsplit, max_comm]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_coe_apply_sub]

lemma eq_one_of_apply_eq {x : L} (hx : IsGen p L x) {g : L ≃ₐ[ℚ_[p]] L} (hg : g x = x) :
    g = 1 := by
  apply AlgEquiv.ext
  intro z
  rw [AlgEquiv.one_apply]
  obtain ⟨k, hk⟩ := exists_norm_pow_mul_le_one p (z : Ω)
  have hk' : ‖(((p : L) ^ k * z : L) : Ω)‖ ≤ 1 := by push_cast; exact hk
  obtain ⟨P, -, hP⟩ := hx.gen _ hk'
  have h1 : g ((p : L) ^ k * z) = (p : L) ^ k * z := by
    rw [← hP, ← aeval_algHom_apply g x P, hg]
  rw [map_mul, map_pow, map_natCast] at h1
  have hpk : ((p : L) ^ k) ≠ 0 := pow_ne_zero k (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact mul_left_cancel₀ hpk h1

lemma D_pos {x : L} (hx : IsGen p L x) {g : L ≃ₐ[ℚ_[p]] L} (hg : g ≠ 1) : 0 < D p x g := by
  unfold D
  rw [norm_pos_iff, sub_ne_zero]
  intro h
  exact hg (eq_one_of_apply_eq p hx (Subtype.ext h))

lemma norm_apply_sub_le_D {x : L} (hx : IsGen p L x) (g : L ≃ₐ[ℚ_[p]] L) {z : L}
    (hz : ‖(z : Ω)‖ ≤ 1) : ‖((g z : L) : Ω) - z‖ ≤ D p x g := by
  obtain ⟨P, hP, rfl⟩ := hx.gen z hz
  rw [← aeval_algHom_apply g x P, coe_aeval, coe_aeval]
  exact norm_aeval_sub_aeval_le p hP (by rw [norm_coe_apply]; exact hx.norm_le) hx.norm_le

variable [FiniteDimensional ℚ_[p] L]

def fs (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) : Finset (L ≃ₐ[ℚ_[p]] L) := Finset.univ.filter (· ∈ S)

@[scoped simp] lemma mem_fs {S : Subgroup (L ≃ₐ[ℚ_[p]] L)} {g : L ≃ₐ[ℚ_[p]] L} : g ∈ fs p S ↔ g ∈ S := by
  simp [fs]

lemma card_fs (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) : (fs p S).card = Nat.card S := by
  rw [fs, Nat.card_eq_fintype_card, Fintype.card_subtype]

def PS (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) (x : L) : L[X] := ∏ s ∈ fs p S, (X - C (s x))

lemma PS_monic (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) (x : L) : (PS p S x).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma intL_PS (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) {x : L} (hx : ‖(x : Ω)‖ ≤ 1) : IntL p L (PS p S x) :=
  intL_prod p L _ fun s _ => intL_X_sub_C p L (by rw [norm_coe_apply]; exact hx)

lemma PS_map (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) (x : L) (τ : L ≃ₐ[ℚ_[p]] L) :
    (PS p S x).map (τ : L →+* L) = ∏ s ∈ fs p S, (X - C ((τ * s) x)) := by
  rw [PS, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Polynomial.map_sub, map_X, map_C, AlgEquiv.mul_apply]
  rfl

lemma eval_PS_map (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) (x : L) (τ : L ≃ₐ[ℚ_[p]] L) :
    ‖((((PS p S x).map (τ : L →+* L)).eval x : L) : Ω)‖ = ∏ s ∈ fs p S, D p x (τ * s) := by
  rw [PS_map, eval_prod, SubmonoidClass.coe_finsetProd, norm_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [eval_sub, eval_X, eval_C, AddSubgroupClass.coe_sub, D, norm_sub_rev]

lemma PS_map_of_mem (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) (x : L) {s₀ : L ≃ₐ[ℚ_[p]] L} (hs₀ : s₀ ∈ S) :
    (PS p S x).map (s₀ : L →+* L) = PS p S x := by
  rw [PS_map, PS]
  refine Finset.prod_nbij (fun s => s₀ * s) (fun s hs => ?_) (fun s _ t _ h => mul_left_cancel h)
    (fun t ht => ?_) (fun s _ => rfl)
  · rw [mem_fs] at hs ⊢
    exact S.mul_mem hs₀ hs
  · have ht' : t ∈ S := (mem_fs p).mp (Finset.mem_coe.mp ht)
    exact ⟨s₀⁻¹ * t, Finset.mem_coe.mpr ((mem_fs p).mpr (S.mul_mem (S.inv_mem hs₀) ht')),
      by simp⟩

theorem norm_apply_sub_le_prod_D {x : L} (hx : IsGen p L x) (S : Subgroup (L ≃ₐ[ℚ_[p]] L))
    {b : L} (hb : ‖(b : Ω)‖ ≤ 1) (hbS : ∀ s ∈ S, s b = b) (τ : L ≃ₐ[ℚ_[p]] L) :
    ‖((τ b : L) : Ω) - b‖ ≤ ∏ s ∈ fs p S, D p x (τ * s) := by
  obtain ⟨f, hf, hfb⟩ := hx.gen b hb

  set F : L[X] := f.map (algebraMap ℚ_[p] L) - C b with hFdef
  have hFint : IntL p L F := by
    refine intL_sub p L (intL_map_algebraMap p L hf) ?_
    intro i; rw [coeff_C]; split_ifs <;> simp [hb]
  have hroot : ∀ s ∈ fs p S, (X - C (s x)) ∣ F := by
    intro s hs
    rw [dvd_iff_isRoot, IsRoot.def, hFdef, eval_sub, eval_C, eval_map_algebraMap,
      aeval_algHom_apply s x f, hfb, hbS s ((mem_fs p).mp hs), sub_self]
  have hinj : Function.Injective fun s : L ≃ₐ[ℚ_[p]] L => s x := by
    intro s t hst
    have h : (t⁻¹ * s) x = x := by
      rw [AlgEquiv.mul_apply]
      have := congrArg (t⁻¹ : L ≃ₐ[ℚ_[p]] L) hst
      simpa using this
    have h2 := eq_one_of_apply_eq p hx h
    calc s = t * (t⁻¹ * s) := by group
      _ = t := by rw [h2, mul_one]
  have hdvd : PS p S x ∣ F :=
    Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) hroot

  set R : L[X] := F /ₘ PS p S x with hRdef
  have hRint : IntL p L R := intL_divByMonic p L hFint (intL_PS p S hx.norm_le) (PS_monic p S x)
  have hFPR : F = PS p S x * R := by
    have h := modByMonic_add_div F (PS p S x)
    rw [(modByMonic_eq_zero_iff_dvd (PS_monic p S x)).mpr hdvd, zero_add] at h
    exact h.symm

  have hev : (F.map (τ : L →+* L)).eval x = b - τ b := by
    rw [hFdef, Polynomial.map_sub, map_C, Polynomial.map_map, eval_sub, eval_C]
    have hcomp : (τ : L →+* L).comp (algebraMap ℚ_[p] L) = algebraMap ℚ_[p] L :=
      RingHom.ext fun c => τ.commutes c
    rw [hcomp, eval_map_algebraMap, hfb]
    rfl
  have hev2 : (F.map (τ : L →+* L)).eval x =
      ((PS p S x).map (τ : L →+* L)).eval x * (R.map (τ : L →+* L)).eval x := by
    rw [hFPR, Polynomial.map_mul, eval_mul]
  have hR1 : ‖(((R.map (τ : L →+* L)).eval x : L) : Ω)‖ ≤ 1 :=
    norm_eval_le p L zero_le_one (intL_map p L hRint τ) hx.norm_le
  calc ‖((τ b : L) : Ω) - b‖ = ‖(((F.map (τ : L →+* L)).eval x : L) : Ω)‖ := by
        rw [hev, AddSubgroupClass.coe_sub, norm_sub_rev]
    _ = (∏ s ∈ fs p S, D p x (τ * s)) * ‖(((R.map (τ : L →+* L)).eval x : L) : Ω)‖ := by
        rw [hev2, MulMemClass.coe_mul, norm_mul, eval_PS_map]
    _ ≤ (∏ s ∈ fs p S, D p x (τ * s)) * 1 := by
        gcongr
        exact Finset.prod_nonneg fun s _ => D_nonneg p x _
    _ = ∏ s ∈ fs p S, D p x (τ * s) := mul_one _

theorem prod_D_le_norm_apply_sub {x : L} (hx : IsGen p L x) (S : Subgroup (L ≃ₐ[ℚ_[p]] L))
    (b : L) (τ : L ≃ₐ[ℚ_[p]] L)
    (hS : ∀ c : L, ‖(c : Ω)‖ ≤ 1 → (∀ s ∈ S, s c = c) → ‖((τ c : L) : Ω) - c‖ ≤ ‖((τ b : L) : Ω) - b‖) :
    ∏ s ∈ fs p S, D p x (τ * s) ≤ ‖((τ b : L) : Ω) - b‖ := by
  set Δ : L[X] := (PS p S x).map (τ : L →+* L) - PS p S x with hΔ
  have hcoeff : ∀ i, ‖((Δ.coeff i : L) : Ω)‖ ≤ ‖((τ b : L) : Ω) - b‖ := by
    intro i
    rw [hΔ, coeff_sub, coeff_map, AddSubgroupClass.coe_sub]
    refine hS _ (intL_PS p S hx.norm_le i) fun s hs => ?_
    have h := congrArg (fun P : L[X] => P.coeff i) (PS_map_of_mem p S x hs)
    simp only [coeff_map] at h
    exact h
  have hev0 : (PS p S x).eval x = 0 := by
    rw [PS, eval_prod]
    apply Finset.prod_eq_zero (i := 1) ((mem_fs p).mpr S.one_mem)
    simp
  have hev : Δ.eval x = ((PS p S x).map (τ : L →+* L)).eval x := by
    rw [hΔ, eval_sub, hev0, sub_zero]
  calc ∏ s ∈ fs p S, D p x (τ * s) = ‖((Δ.eval x : L) : Ω)‖ := by rw [hev, eval_PS_map]
    _ ≤ ‖((τ b : L) : Ω) - b‖ := norm_eval_le p L (norm_nonneg _) hcoeff hx.norm_le

lemma prod_prod_mul_eq_pow (S : Subgroup (L ≃ₐ[ℚ_[p]] L)) {A : Finset (L ≃ₐ[ℚ_[p]] L)}
    (hA : ∀ g ∈ A, ∀ h ∈ S, g * h ∈ A) (F : (L ≃ₐ[ℚ_[p]] L) → ℝ) :
    ∏ g ∈ A, ∏ h ∈ fs p S, F (g * h) = (∏ g ∈ A, F g) ^ (fs p S).card := by
  rw [Finset.prod_comm]
  rw [← Finset.prod_const]
  refine Finset.prod_congr rfl fun h hh => ?_
  have hh' : h ∈ S := (mem_fs p).mp hh
  refine Finset.prod_nbij (fun g => g * h) (fun g hg => hA g hg h hh')
    (fun g _ g' _ hgg' => mul_right_cancel hgg') (fun g' hg' => ?_) (fun g _ => rfl)
  refine ⟨g' * h⁻¹, Finset.mem_coe.mpr (hA g' (Finset.mem_coe.mp hg') h⁻¹ (S.inv_mem hh')), ?_⟩
  simp

lemma apply_eq_of_mem_adjoin_simple {F E : Type*} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) {a z : E} (ha : σ a = a) (hz : z ∈ IntermediateField.adjoin F {a}) :
    σ z = z := by
  have hle : IntermediateField.adjoin F {a} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      IntermediateField.mem_fixedField_iff]
    intro f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    have hnat : ∀ k : ℕ, (σ ^ k) a = a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
    rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩
    · rw [zpow_natCast]; exact hnat k
    · rw [zpow_neg, zpow_natCast]
      calc (σ ^ k)⁻¹ a = (σ ^ k)⁻¹ ((σ ^ k) a) := by rw [hnat k]
        _ = a := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hz' := hle hz
  rw [IntermediateField.mem_fixedField_iff] at hz'
  exact hz' σ (Subgroup.mem_zpowers σ)

end LevelField

section Cyclotomic

private lemma _root_.TTA.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "TTA" "exists_isPrimitiveRoot"
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    Q n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma mem_of_isPrimitiveRoot (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) : ζ ∈ Q n :=
  PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one

lemma mem_fixingSubgroup_Q_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (Q n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (mem_of_isPrimitiveRoot p n hζ)
  · intro h x hx
    rw [cyclotomicTower_eq_adjoin p n hζ] at hx
    exact apply_eq_of_mem_adjoin_simple σ h hx

scoped instance finiteDimensional_Q (n : ℕ) : FiniteDimensional ℚ_[p] (Q n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n
  rw [cyclotomicTower_eq_adjoin p n hζ]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)

scoped instance normal_Q (n : ℕ) : Normal ℚ_[p] (Q n) := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  set f : ℚ_[p][X] := X ^ (p ^ n) - C 1 with hf
  have hf0 : f ≠ 0 := X_pow_sub_C_ne_zero hpos 1
  have hset : {ζ : Ω | ζ ^ (p ^ n) = 1} = f.rootSet Ω := by
    ext ζ
    rw [Set.mem_setOf_eq, mem_rootSet, hf]
    simp only [map_one, aeval_sub, map_pow, aeval_X]
    constructor
    · intro h; exact ⟨hf0, by rw [h, sub_self]⟩
    · rintro ⟨-, h⟩; exact sub_eq_zero.mp h
  have hQ : Q n = IntermediateField.adjoin ℚ_[p] (f.rootSet Ω) := by
    unfold PadicAlgCl.cyclotomicTower; rw [hset]
  rw [hQ]
  haveI : IsSplittingField ℚ_[p] (IntermediateField.adjoin ℚ_[p] (f.rootSet Ω)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  exact Normal.of_isSplittingField f

lemma finrank_Q {k : ℕ} (hk : 1 ≤ k) : Module.finrank ℚ_[p] (Q k) = (p ^ k).totient := by
  rw [(PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 k hk,
    Nat.totient_prime_pow (Fact.out : p.Prime) hk, mul_comm]

lemma totient_pow_pos (m : ℕ) : 0 < (p ^ m).totient :=
  Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos m)

lemma totient_pow_eq_mul {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (p ^ n).totient = (p ^ k).totient * p ^ (n - k) := by
  have hp : p.Prime := Fact.out
  rw [Nat.totient_prime_pow hp hk, Nat.totient_prime_pow hp (hk.trans hkn)]
  have h : n - 1 = (k - 1) + (n - k) := by omega
  rw [h, pow_add]
  ring

lemma pow_sub_pow_eq_totient {m : ℕ} (hm : 1 ≤ m) : p ^ m - p ^ (m - 1) = (p ^ m).totient := by
  have hp : p.Prime := Fact.out
  rw [Nat.totient_prime_pow hp hm]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_sub_one]

lemma totient_pow_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : (p ^ a).totient ≤ (p ^ b).totient := by
  rw [totient_pow_eq_mul p ha hab]
  exact Nat.le_mul_of_pos_right _ (pow_pos (Fact.out : p.Prime).pos _)

end Cyclotomic

section Level

variable (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M] [Normal ℚ_[p] M]
variable (n : ℕ)

abbrev LL : IntermediateField ℚ_[p] (PadicAlgCl p) := M ⊔ Q n

scoped instance finiteDimensional_LL : FiniteDimensional ℚ_[p] (LL p M n) :=
  IntermediateField.finiteDimensional_sup M (Q n)

scoped instance normal_LL : Normal ℚ_[p] (LL p M n) := IntermediateField.normal_sup ℚ_[p] Ω M (Q n)

omit [FiniteDimensional ℚ_[p] M] [Normal ℚ_[p] M] in
lemma Q_le_LL {k : ℕ} (hk : k ≤ n) : Q k ≤ LL p M n :=
  (PadicAlgCl.cyclotomicTower_mono p hk).trans le_sup_right

def T (k : ℕ) : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n) :=
  Finset.univ.filter fun g => lift p (LL p M n) g ∈ (Q k).fixingSubgroup

def HS : Subgroup (LL p M n ≃ₐ[ℚ_[p]] LL p M n) :=
  (IntermediateField.restrict (Q_le_LL p M n le_rfl)).fixingSubgroup

def Slev (k : ℕ) : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n) := T p M n k \ T p M n (k + 1)

variable {M n}

omit [Normal ℚ_[p] M] in
lemma mem_T_iff {k : ℕ} {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n} :
    g ∈ T p M n k ↔ ∀ z : Ω, z ∈ Q k → lift p (LL p M n) g z = z := by
  rw [T, Finset.mem_filter, IntermediateField.mem_fixingSubgroup_iff]
  simp

lemma mem_T_iff' {k : ℕ} (hk : k ≤ n) {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n} :
    g ∈ T p M n k ↔ ∀ z : LL p M n, (z : Ω) ∈ Q k → g z = z := by
  rw [mem_T_iff]
  constructor
  · intro h z hz
    apply Subtype.ext
    rw [← lift_coe]
    exact h z hz
  · intro h z hz
    have hzL : z ∈ LL p M n := Q_le_LL p M n hk hz
    have := congrArg Subtype.val (h ⟨z, hzL⟩ hz)
    rwa [← lift_coe] at this

lemma mem_T_restrict_iff {k : ℕ} (hk : k ≤ n) {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n} :
    g ∈ (IntermediateField.restrict (Q_le_LL p M n hk)).fixingSubgroup ↔ g ∈ T p M n k := by
  rw [mem_T_iff' p hk, IntermediateField.mem_fixingSubgroup_iff]
  simp only [IntermediateField.mem_restrict]

lemma mem_HS_iff {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n} : g ∈ HS p M n ↔ g ∈ T p M n n :=
  mem_T_restrict_iff p le_rfl

lemma fs_HS : fs p (HS p M n) = T p M n n := by
  ext g; rw [mem_fs, mem_HS_iff]

lemma T_mono {k k' : ℕ} (h : k ≤ k') : T p M n k' ⊆ T p M n k := by
  intro g hg
  rw [mem_T_iff] at hg ⊢
  exact fun z hz => hg z (PadicAlgCl.cyclotomicTower_mono p h hz)

lemma card_T_mul {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (T p M n k).card * (p ^ k).totient = Module.finrank ℚ_[p] (LL p M n) := by
  set QL := IntermediateField.restrict (Q_le_LL p M n hkn) with hQL
  have h1 : (T p M n k).card = Nat.card QL.fixingSubgroup := by
    rw [← card_fs p]
    congr 1
    ext g
    rw [mem_fs, mem_T_restrict_iff p hkn]
  have h2 : Nat.card QL.fixingSubgroup = Module.finrank QL (LL p M n) :=
    IsGalois.card_fixingSubgroup_eq_finrank QL
  have h3 : Module.finrank ℚ_[p] QL = (p ^ k).totient := by
    rw [← finrank_Q p hk1]
    exact ((IntermediateField.restrict_algEquiv (Q_le_LL p M n hkn)).toLinearEquiv.finrank_eq).symm
  rw [h1, h2, ← h3, mul_comm, Module.finrank_mul_finrank]

lemma card_T {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (T p M n k).card = (T p M n n).card * p ^ (n - k) := by
  have h1 := card_T_mul p (M := M) hk1 hkn
  have h2 := card_T_mul p (M := M) (hk1.trans hkn) le_rfl
  rw [← h2, totient_pow_eq_mul p hk1 hkn] at h1
  have hpos : 0 < (p ^ k).totient := totient_pow_pos p k
  have : (T p M n k).card * (p ^ k).totient = ((T p M n n).card * p ^ (n - k)) * (p ^ k).totient := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

lemma card_Slev {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    (Slev p M n k).card = (T p M n n).card * (p ^ (n - k)).totient := by
  rw [Slev, Finset.card_sdiff, Finset.inter_eq_left.mpr (T_mono p (Nat.le_succ k)),
    card_T p hk1 hkn.le, card_T p (Nat.le_succ_of_le hk1) hkn, ← Nat.mul_sub,
    ← pow_sub_pow_eq_totient p (Nat.le_sub_of_add_le' hkn)]
  congr 2

lemma Slev_disjoint {k k' : ℕ} (h : k ≠ k') : Disjoint (Slev p M n k) (Slev p M n k') := by
  wlog hlt : k < k' generalizing k k'
  · exact (this h.symm (lt_of_le_of_ne (not_lt.mp hlt) h.symm)).symm
  rw [Finset.disjoint_left]
  intro g hg hg'
  rw [Slev, Finset.mem_sdiff] at hg hg'
  exact hg.2 (T_mono p (Nat.succ_le_of_lt hlt) hg'.1)

lemma mul_mem_Slev {k : ℕ} (hkn : k < n) {g h : LL p M n ≃ₐ[ℚ_[p]] LL p M n}
    (hg : g ∈ Slev p M n k) (hh : h ∈ HS p M n) : g * h ∈ Slev p M n k := by
  rw [mem_HS_iff, mem_T_iff' p le_rfl] at hh
  rw [Slev, Finset.mem_sdiff, mem_T_iff' p hkn.le, mem_T_iff' p (Nat.succ_le_of_lt hkn)] at hg ⊢
  refine ⟨fun z hz => ?_, fun H => hg.2 fun z hz => ?_⟩
  · rw [AlgEquiv.mul_apply, hh z (PadicAlgCl.cyclotomicTower_mono p hkn.le hz), hg.1 z hz]
  · have := H z hz
    rwa [AlgEquiv.mul_apply, hh z (PadicAlgCl.cyclotomicTower_mono p (Nat.succ_le_of_lt hkn) hz)]
      at this

omit [Normal ℚ_[p] M] in

lemma norm_lift_sub_eq {k : ℕ} (hkn : k < n) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n} (hg : g ∈ Slev p M n k) :
    ‖lift p (LL p M n) g ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) := by
  rw [Slev, Finset.mem_sdiff] at hg
  have h1 : lift p (LL p M n) g ∈ (Q k).fixingSubgroup := (Finset.mem_filter.mp hg.1).2
  have h2 : lift p (LL p M n) g ∉ (Q (k + 1)).fixingSubgroup := fun h =>
    hg.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact (PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup p hkn hζ
    _ h1 h2).2

lemma coe_mem_Q_of_forall_HS {c : LL p M n} (hc : ∀ s ∈ HS p M n, s c = c) : (c : Ω) ∈ Q n := by
  have h : c ∈ IntermediateField.fixedField (HS p M n) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr hc
  rw [HS, IsGalois.fixedField_fixingSubgroup] at h
  exact (IntermediateField.mem_restrict _ c).mp h

def Pi (x : LL p M n) (r : ℝ) : ℝ := ∏ g, max (D p x g) r

lemma card_T_n_pos : 0 < (T p M n n).card :=
  Finset.card_pos.mpr ⟨1, by rw [← fs_HS, mem_fs]; exact (HS p M n).one_mem⟩

lemma prod_Slev_le {x : LL p M n} (hx : IsGen p (LL p M n) x) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ∏ g ∈ Slev p M n k, max (D p x g) r ≤ max ((p : ℝ)⁻¹) (r ^ (p ^ (n - k)).totient) := by
  set φ : ℕ := (p ^ (n - k)).totient with hφ
  have hφpos : 0 < φ := totient_pow_pos p (n - k)
  set β : ℝ := (p : ℝ) ^ (-(1 : ℝ) / (φ : ℝ)) with hβ
  have hβ0 : 0 ≤ β := (Real.rpow_pos_of_pos (p_pos p) _).le
  have hβφ : β ^ φ = (p : ℝ)⁻¹ := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le, ← Real.rpow_neg_one]
    congr 1
    have : (φ : ℝ) ≠ 0 := by exact_mod_cast hφpos.ne'
    field_simp
  have hζL : ζ ∈ LL p M n := Q_le_LL p M n le_rfl (mem_of_isPrimitiveRoot p n hζ)
  set ζL : LL p M n := ⟨ζ, hζL⟩ with hζLdef
  set B := fs p (HS p M n) with hBdef
  have hB : B.card = (T p M n n).card := by rw [hBdef, fs_HS]
  have hBpos : B.card ≠ 0 := by rw [hB]; exact (card_T_n_pos p).ne'

  have hhard : ∀ g : LL p M n ≃ₐ[ℚ_[p]] LL p M n,
      ∏ h ∈ B, D p x (g * h) ≤ ‖((g ζL : LL p M n) : Ω) - ζL‖ := by
    intro g
    refine prod_D_le_norm_apply_sub p hx (HS p M n) ζL g fun c hc hcS => ?_
    have hcQ : (c : Ω) ∈ Q n := coe_mem_Q_of_forall_HS p hcS
    have h := PadicAlgCl.norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower p hζ
      (lift p (LL p M n) g) hcQ hc
    rwa [lift_coe, show ζ = ((ζL : LL p M n) : Ω) from rfl, lift_coe] at h
  have hval : ∀ g ∈ Slev p M n k, ‖((g ζL : LL p M n) : Ω) - ζL‖ = β := by
    intro g hg
    rw [show ((ζL : LL p M n) : Ω) = ζ from rfl, ← lift_coe]
    exact norm_lift_sub_eq p hkn hζ hg
  have hstab : ∀ g ∈ Slev p M n k, ∀ h ∈ HS p M n, g * h ∈ Slev p M n k :=
    fun g hg h hh => mul_mem_Slev p hkn hg hh
  have key : (∏ g ∈ Slev p M n k, max (D p x g) r) ^ B.card ≤ ((max β r) ^ φ) ^ B.card := by
    calc (∏ g ∈ Slev p M n k, max (D p x g) r) ^ B.card
        = ∏ g ∈ Slev p M n k, ∏ h ∈ B, max (D p x (g * h)) r :=
          (prod_prod_mul_eq_pow p (HS p M n) hstab (fun g => max (D p x g) r)).symm
      _ ≤ ∏ g ∈ Slev p M n k, max (∏ h ∈ B, D p x (g * h)) r :=
          Finset.prod_le_prod (fun g _ => Finset.prod_nonneg fun h _ => le_max_of_le_right hr0)
            (fun g _ => prod_max_le_max_prod B (fun h _ => D_nonneg p x _)
              (fun h _ => D_le_one p hx _) hr0 hr1)
      _ ≤ ∏ g ∈ Slev p M n k, max β r :=
          Finset.prod_le_prod (fun g _ => le_max_of_le_right hr0)
            (fun g hg => max_le_max ((hhard g).trans (hval g hg).le) le_rfl)
      _ = (max β r) ^ (Slev p M n k).card := Finset.prod_const _
      _ = ((max β r) ^ φ) ^ B.card := by
          rw [card_Slev p hk1 hkn, hB, ← pow_mul, mul_comm]
  have h2 : ∏ g ∈ Slev p M n k, max (D p x g) r ≤ (max β r) ^ φ :=
    (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun g _ => le_max_of_le_right hr0)
      (pow_nonneg (le_max_of_le_right hr0) _) hBpos).mp key
  calc ∏ g ∈ Slev p M n k, max (D p x g) r ≤ (max β r) ^ φ := h2
    _ ≤ max (β ^ φ) (r ^ φ) := max_pow_le β r φ
    _ = max ((p : ℝ)⁻¹) (r ^ φ) := by rw [hβφ]

theorem Pi_le {x : LL p M n} (hx : IsGen p (LL p M n) x) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    Pi p x r ≤ ∏ k ∈ Finset.Ico 1 n, max ((p : ℝ)⁻¹) (r ^ (p ^ (n - k)).totient) := by
  have hdisj : ((Finset.Ico 1 n : Finset ℕ) : Set ℕ).PairwiseDisjoint (Slev p M n) :=
    fun k _ k' _ hne => Slev_disjoint p hne
  calc Pi p x r = ∏ g, max (D p x g) r := rfl
    _ ≤ ∏ g ∈ (Finset.Ico 1 n).biUnion (Slev p M n), max (D p x g) r :=
        prod_le_prod_of_subset (Finset.subset_univ _) (fun g _ => le_max_of_le_right hr0)
          (fun g _ => max_le (D_le_one p hx g) hr1)
    _ = ∏ k ∈ Finset.Ico 1 n, ∏ g ∈ Slev p M n k, max (D p x g) r := Finset.prod_biUnion hdisj
    _ ≤ ∏ k ∈ Finset.Ico 1 n, max ((p : ℝ)⁻¹) (r ^ (p ^ (n - k)).totient) :=
        Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun g _ => le_max_of_le_right hr0)
          (fun k hk => prod_Slev_le p hx hr0 hr1 (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 hζ)

variable (M) in

structure MGen (y : Ω) : Prop where
  mem : y ∈ M
  norm_le : ‖y‖ ≤ 1
  gen : ∀ m : Ω, m ∈ M → ‖m‖ ≤ 1 → ∃ P : ℚ_[p][X], IntPoly p P ∧ aeval y P = m

variable (M) in
omit [Normal ℚ_[p] M] in
lemma exists_mgen : ∃ y : Ω, MGen p M y := by
  obtain ⟨y, hy⟩ := exists_isGen p M
  refine ⟨y, y.2, hy.norm_le, fun m hm hm1 => ?_⟩
  obtain ⟨P, hP, hPm⟩ := hy.gen ⟨m, hm⟩ hm1
  exact ⟨P, hP, by rw [← coe_aeval, hPm]⟩

def dd (y : Ω) : ℕ := (minpoly ℚ_[p] y).natDegree

def Rts (y : Ω) : Finset Ω := ((minpoly ℚ_[p] y).map (algebraMap ℚ_[p] Ω)).roots.toFinset

def gam (y : Ω) : ℝ :=
  if h : ((Rts p y).erase y).Nonempty then min 1 (((Rts p y).erase y).inf' h fun ρ => ‖ρ - y‖)
  else 1

lemma one_le_dd (y : Ω) : 1 ≤ dd p y :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)

lemma card_Rts_le (y : Ω) : (Rts p y).card ≤ dd p y := by
  refine (Multiset.toFinset_card_le _).trans ?_
  refine (card_roots' _).trans ?_
  rw [dd, natDegree_map_eq_of_injective (algebraMap ℚ_[p] Ω).injective]

lemma gam_pos (y : Ω) : 0 < gam p y := by
  unfold gam
  split_ifs with h
  · refine lt_min zero_lt_one ?_
    rw [Finset.lt_inf'_iff]
    intro ρ hρ
    rw [norm_pos_iff, sub_ne_zero]
    exact (Finset.mem_erase.mp hρ).1
  · exact zero_lt_one

lemma gam_le_one (y : Ω) : gam p y ≤ 1 := by
  unfold gam
  split_ifs with h
  · exact min_le_left _ _
  · exact le_rfl

lemma gam_le {y ρ : Ω} (hρ : ρ ∈ Rts p y) (hne : ρ ≠ y) : gam p y ≤ ‖ρ - y‖ := by
  have hmem : ρ ∈ (Rts p y).erase y := Finset.mem_erase.mpr ⟨hne, hρ⟩
  unfold gam
  rw [dif_pos ⟨ρ, hmem⟩]
  exact (min_le_right _ _).trans (Finset.inf'_le _ hmem)

section WithY

def yL {y : Ω} (hy : MGen p M y) : LL p M n := ⟨y, (le_sup_left : M ≤ M ⊔ Q n) hy.mem⟩

omit [FiniteDimensional ℚ_[p] M] [Normal ℚ_[p] M] in
lemma coe_yL {y : Ω} (hy : MGen p M y) : ((yL p (n := n) hy : LL p M n) : Ω) = y := rfl

lemma coe_apply_yL_mem_Rts {y : Ω} (hy : MGen p M y) (g : LL p M n ≃ₐ[ℚ_[p]] LL p M n) :
    ((g (yL p hy) : LL p M n) : Ω) ∈ Rts p y := by
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [Rts, Multiset.mem_toFinset, mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint)),
    IsRoot.def, eval_map_algebraMap, ← lift_coe, coe_yL, aeval_algHom_apply, minpoly.aeval, map_zero]

lemma gam_le_norm {y : Ω} (hy : MGen p M y) {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n}
    (hg : g (yL p hy) ≠ yL p hy) :
    gam p y ≤ ‖((g (yL p hy) : LL p M n) : Ω) - yL p (n := n) hy‖ :=
  gam_le p (coe_apply_yL_mem_Rts p hy g) fun h => hg (Subtype.ext h)

lemma eq_one_of_mem_HS_of_apply_yL {y : Ω} (hy : MGen p M y) {h : LL p M n ≃ₐ[ℚ_[p]] LL p M n}
    (hh : h ∈ HS p M n) (hhy : h (yL p hy) = yL p hy) : h = 1 := by
  have hQ : lift p (LL p M n) h ∈ (Q n).fixingSubgroup := by
    rw [mem_HS_iff] at hh
    exact (Finset.mem_filter.mp hh).2
  have hM : lift p (LL p M n) h ∈ M.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro m hm
    obtain ⟨k, hk⟩ := exists_norm_pow_mul_le_one p m
    obtain ⟨P, -, hP⟩ := hy.gen _ (M.mul_mem (pow_mem (IntermediateField.natCast_mem M p) k) hm) hk
    have hy' : lift p (LL p M n) h y = y := by
      have := congrArg Subtype.val hhy
      rwa [← lift_coe] at this
    have h1 : lift p (LL p M n) h ((p : Ω) ^ k * m) = (p : Ω) ^ k * m := by
      rw [← hP, ← aeval_algHom_apply, hy']
    rw [map_mul, map_pow, map_natCast] at h1
    exact mul_left_cancel₀ (pow_ne_zero k (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) h1
  have hL : lift p (LL p M n) h ∈ (LL p M n).fixingSubgroup := by
    change lift p (LL p M n) h ∈ (M ⊔ Q n).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hM, hQ⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hL
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  rw [← lift_coe, AlgEquiv.one_apply]
  exact hL z z.2

lemma card_T_n_le {y : Ω} (hy : MGen p M y) : (T p M n n).card ≤ dd p y := by
  rw [← fs_HS]
  refine le_trans ?_ (card_Rts_le p y)
  refine Finset.card_le_card_of_injOn (fun h => ((h (yL p hy) : LL p M n) : Ω))
    (fun h _ => coe_apply_yL_mem_Rts p hy h) ?_
  intro h hh h' hh' hhh'
  have hh1 : h ∈ HS p M n := (mem_fs p).mp hh
  have hh2 : h' ∈ HS p M n := (mem_fs p).mp hh'
  have heq : (h'⁻¹ * h) (yL p hy) = yL p hy := by
    rw [AlgEquiv.mul_apply]
    have h3 : h (yL p hy) = h' (yL p hy) := Subtype.ext hhh'
    rw [h3, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have := eq_one_of_mem_HS_of_apply_yL p hy ((HS p M n).mul_mem ((HS p M n).inv_mem hh2) hh1) heq
  calc h = h' * (h'⁻¹ * h) := by group
    _ = h' := by rw [this, mul_one]

lemma card_univ_le {y : Ω} (hy : MGen p M y) :
    (Finset.univ : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n)).card ≤
      dd p y * (fs p (MulAction.stabilizer (LL p M n ≃ₐ[ℚ_[p]] LL p M n) (yL p (n := n) hy))).card := by
  set N := MulAction.stabilizer (LL p M n ≃ₐ[ℚ_[p]] LL p M n) (yL p (n := n) hy) with hN
  set f : (LL p M n ≃ₐ[ℚ_[p]] LL p M n) → PadicAlgCl p := fun g => ((g (yL p hy) : LL p M n) : Ω)
    with hf
  have hmaps : ∀ g ∈ (Finset.univ : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n)), f g ∈ Rts p y :=
    fun g _ => coe_apply_yL_mem_Rts p hy g
  have hfib : ∀ b ∈ Rts p y,
      ((Finset.univ : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n)).filter fun g => f g = b).card ≤
        (fs p N).card := by
    intro b _
    by_cases hne : ((Finset.univ : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n)).filter
        fun g => f g = b).Nonempty
    · obtain ⟨g₀, hg₀⟩ := hne
      rw [Finset.mem_filter] at hg₀
      refine Finset.card_le_card_of_injOn (fun g => g₀⁻¹ * g) (fun g hg => ?_)
        (fun g _ g' _ h => mul_left_cancel h)
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, mem_fs, hN, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def,
        AlgEquiv.mul_apply]
      have h1 : g (yL p (n := n) hy) = g₀ (yL p hy) := Subtype.ext (hg.2.trans hg₀.2.symm)
      rw [h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  calc (Finset.univ : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n)).card ≤ (fs p N).card * (Rts p y).card :=
        Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
    _ ≤ (fs p N).card * dd p y := Nat.mul_le_mul_left _ (card_Rts_le p y)
    _ = dd p y * (fs p N).card := mul_comm _ _

theorem le_Pi {y : Ω} (hy : MGen p M y) {x : LL p M n} (hx : IsGen p (LL p M n) x)
    {σ : LL p M n ≃ₐ[ℚ_[p]] LL p M n}
    (hσH : σ ∈ HS p M n) (hσ1 : σ ≠ 1) : gam p y ^ dd p y ≤ Pi p x (D p x σ) := by
  let N : Subgroup (LL p M n ≃ₐ[ℚ_[p]] LL p M n) :=
    MulAction.stabilizer (LL p M n ≃ₐ[ℚ_[p]] LL p M n) (yL p (n := n) hy)
  have hmemN : ∀ {g : LL p M n ≃ₐ[ℚ_[p]] LL p M n}, g ∈ N ↔ g (yL p (n := n) hy) = yL p hy :=
    fun {g} => by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  have hr0 : 0 ≤ D p x σ := D_nonneg p x σ
  have hσy : σ (yL p hy) ≠ yL p (n := n) hy :=
    fun h => hσ1 (eq_one_of_mem_HS_of_apply_yL p hy hσH h)
  have hy1 : ‖((yL p hy : LL p M n) : Ω)‖ ≤ 1 := hy.norm_le
  have hγ0 : 0 ≤ gam p y := (gam_pos p y).le
  let A : Finset (LL p M n ≃ₐ[ℚ_[p]] LL p M n) := Finset.univ \ fs p N

  have heasy : ∀ g : LL p M n ≃ₐ[ℚ_[p]] LL p M n,
      ‖((g (yL p hy) : LL p M n) : Ω) - yL p (n := n) hy‖ ≤ ∏ ν ∈ fs p N, D p x (g * ν) :=
    fun g => norm_apply_sub_le_prod_D p hx N hy1 (fun s hs => hmemN.mp hs) g

  have hpartN : gam p y ≤ ∏ g ∈ fs p N, max (D p x g) (D p x σ) := by
    calc gam p y ≤ ‖((σ (yL p hy) : LL p M n) : Ω) - yL p (n := n) hy‖ := gam_le_norm p hy hσy
      _ ≤ ∏ ν ∈ fs p N, D p x (σ * ν) := heasy σ
      _ ≤ ∏ g ∈ fs p N, max (D p x g) (D p x σ) :=
          Finset.prod_le_prod (fun g _ => D_nonneg p x _) fun g _ =>
            (D_mul_le p x σ g).trans (by rw [max_comm])

  have hAstab : ∀ g ∈ A, ∀ h ∈ N, g * h ∈ A := by
    intro g hg h hh
    rw [Finset.mem_sdiff, mem_fs] at hg ⊢
    refine ⟨Finset.mem_univ _, fun hgh => hg.2 ?_⟩
    have := N.mul_mem hgh (N.inv_mem hh)
    rwa [mul_inv_cancel_right] at this
  have hAne : ∀ g ∈ A, g (yL p hy) ≠ yL p (n := n) hy := by
    intro g hg
    rw [Finset.mem_sdiff, mem_fs] at hg
    exact fun h => hg.2 (hmemN.mpr h)
  have hNpos : (fs p N).card ≠ 0 :=
    (Finset.card_pos.mpr ⟨1, (mem_fs p).mpr N.one_mem⟩).ne'
  have hAcard : A.card ≤ (dd p y - 1) * (fs p N).card := by
    change (Finset.univ \ fs p N).card ≤ _
    rw [Finset.card_univ_diff, Nat.sub_one_mul]
    exact Nat.sub_le_sub_right (by simpa using card_univ_le p hy (n := n)) _
  have hpartA : gam p y ^ (dd p y - 1) ≤ ∏ g ∈ A, D p x g := by
    have key : (gam p y ^ (dd p y - 1)) ^ (fs p N).card ≤ (∏ g ∈ A, D p x g) ^ (fs p N).card := by
      calc (gam p y ^ (dd p y - 1)) ^ (fs p N).card = gam p y ^ ((dd p y - 1) * (fs p N).card) := by
            rw [pow_mul]
        _ ≤ gam p y ^ A.card := pow_le_pow_of_le_one hγ0 (gam_le_one p y) hAcard
        _ = ∏ g ∈ A, gam p y := (Finset.prod_const _).symm
        _ ≤ ∏ g ∈ A, ‖((g (yL p hy) : LL p M n) : Ω) - yL p (n := n) hy‖ :=
            Finset.prod_le_prod (fun g _ => hγ0) fun g hg => gam_le_norm p hy (hAne g hg)
        _ ≤ ∏ g ∈ A, ∏ ν ∈ fs p N, D p x (g * ν) :=
            Finset.prod_le_prod (fun g _ => norm_nonneg _) fun g _ => heasy g
        _ = (∏ g ∈ A, D p x g) ^ (fs p N).card := prod_prod_mul_eq_pow p N hAstab (D p x)
    exact (pow_le_pow_iff_left₀ (pow_nonneg hγ0 _) (Finset.prod_nonneg fun g _ => D_nonneg p x g)
      hNpos).mp key

  have hsplit : Pi p x (D p x σ) =
      (∏ g ∈ A, max (D p x g) (D p x σ)) * ∏ g ∈ fs p N, max (D p x g) (D p x σ) :=
    (Finset.prod_sdiff (Finset.subset_univ _)).symm
  have hd : dd p y = (dd p y - 1) + 1 := (Nat.sub_add_cancel (one_le_dd p y)).symm
  have hA2 : ∏ g ∈ A, D p x g ≤ ∏ g ∈ A, max (D p x g) (D p x σ) :=
    Finset.prod_le_prod (fun g _ => D_nonneg p x g) fun g _ => le_max_left _ _
  calc gam p y ^ dd p y = gam p y ^ (dd p y - 1) * gam p y := by
        conv_lhs => rw [hd]
        rw [pow_succ]
    _ ≤ (∏ g ∈ A, max (D p x g) (D p x σ)) * ∏ g ∈ fs p N, max (D p x g) (D p x σ) :=
        mul_le_mul (hpartA.trans hA2) hpartN hγ0
          (Finset.prod_nonneg fun g _ => le_max_of_le_right hr0)
    _ = Pi p x (D p x σ) := hsplit.symm

end WithY

end Level

section Final

variable {M : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] M] [Normal ℚ_[p] M]

theorem core {y : Ω} (hy : MGen p M y) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ x : LL p M n, IsGen p (LL p M n) x →
      ∀ σ : LL p M n ≃ₐ[ℚ_[p]] LL p M n, σ ∈ HS p M n → σ ≠ 1 → (p : ℝ) ^ (-ε') < D p x σ := by
  have hp1 : (1 : ℝ) < p := one_lt_p p
  set r₀ : ℝ := (p : ℝ) ^ (-ε') with hr₀
  have hr₀0 : 0 ≤ r₀ := (Real.rpow_pos_of_pos (p_pos p) _).le
  have hr₀1 : r₀ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)

  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / ε') hp1
  set m₀ : ℕ := m + 1 with hm₀
  have hm₀φ : r₀ ^ (p ^ m₀).totient ≤ (p : ℝ)⁻¹ := by
    rw [hr₀, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le, ← Real.rpow_neg_one,
      Real.rpow_le_rpow_left_iff hp1, hm₀, Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
    have h1 : (1 : ℝ) ≤ ε' * (p : ℝ) ^ m := by
      rw [div_lt_iff₀ hε'] at hm; linarith
    have h2 : ((p : ℝ) ^ m) ≤ ((p ^ m * (p - 1) : ℕ) : ℝ) := by
      have hp2 : 1 ≤ p - 1 := Nat.le_sub_one_of_lt (Fact.out : p.Prime).one_lt
      exact_mod_cast Nat.le_mul_of_pos_right _ hp2
    nlinarith

  have hγd : 0 < gam p y ^ dd p y := pow_pos (gam_pos p y) _
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one hγd (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨m₀ + N₁ + 2, fun n hn x hx σ hσH hσ1 => ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n
  have hup := Pi_le p hx (D_nonneg p x σ) (D_le_one p hx σ) hζ
  have hlow := le_Pi p hy hx hσH hσ1
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (p_pos p).le
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have hprod : ∏ k ∈ Finset.Ico 1 n, max ((p : ℝ)⁻¹) (D p x σ ^ (p ^ (n - k)).totient) ≤
      ((p : ℝ)⁻¹) ^ N₁ := by
    calc ∏ k ∈ Finset.Ico 1 n, max ((p : ℝ)⁻¹) (D p x σ ^ (p ^ (n - k)).totient)
        ≤ ∏ k ∈ Finset.Ico 1 (n - m₀ + 1), max ((p : ℝ)⁻¹) (D p x σ ^ (p ^ (n - k)).totient) :=
          prod_le_prod_of_subset (Finset.Ico_subset_Ico le_rfl (by omega))
            (fun k _ => le_max_of_le_left hpinv0)
            (fun k _ => max_le hpinv1 (pow_le_one₀ (D_nonneg p x σ) (D_le_one p hx σ)))
      _ = ∏ k ∈ Finset.Ico 1 (n - m₀ + 1), (p : ℝ)⁻¹ := by
          refine Finset.prod_congr rfl fun k hk => max_eq_left ?_
          rw [Finset.mem_Ico] at hk
          calc D p x σ ^ (p ^ (n - k)).totient ≤ r₀ ^ (p ^ (n - k)).totient :=
                pow_le_pow_left₀ (D_nonneg p x σ) hle _
            _ ≤ r₀ ^ (p ^ m₀).totient :=
                pow_le_pow_of_le_one hr₀0 hr₀1 (totient_pow_mono p (by omega) (by omega))
            _ ≤ (p : ℝ)⁻¹ := hm₀φ
      _ = ((p : ℝ)⁻¹) ^ (n - m₀) := by rw [Finset.prod_const, Nat.card_Ico]; congr 1
      _ ≤ ((p : ℝ)⁻¹) ^ N₁ := pow_le_pow_of_le_one hpinv0 hpinv1 (by omega)
  linarith

theorem main (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    [Normal ℚ_[p] M] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : PadicAlgCl p,
      a ∈ M ⊔ PadicAlgCl.cyclotomicTower p n → ‖a‖ ≤ 1 →
      PadicAlgCl.cyclotomicTower p n ≤ IntermediateField.adjoin ℚ_[p] {a} →
      (∀ c ∈ IntermediateField.adjoin ℚ_[p] {a}, ‖c‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval a P = c) →
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup → σ a ≠ a →
        (p : ℝ) ^ (-ε) < ‖σ a - a‖ := by
  obtain ⟨y, hy⟩ := exists_mgen p M
  set d : ℕ := dd p y with hddef
  have hd1 : 1 ≤ d := one_le_dd p y
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨N₀, hN₀⟩ := core p hy (div_pos hε hdpos)
  refine ⟨N₀, fun n hn a haL ha1 hQa hgen σ hσ hne => ?_⟩
  set r₀ : ℝ := (p : ℝ) ^ (-(ε / d)) with hr₀
  have hr₀pos : 0 < r₀ := Real.rpow_pos_of_pos (p_pos p) _
  have hr₀1 : r₀ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_lt_p p).le (by
      have := div_pos hε hdpos; linarith)
  have hr₀d : r₀ ^ d = (p : ℝ) ^ (-ε) := by
    rw [hr₀, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le]
    congr 1
    field_simp

  obtain ⟨x, hx⟩ := exists_isGen p (LL p M n)
  set G' := (LL p M n ≃ₐ[ℚ_[p]] LL p M n)
  set g : G' := res p (LL p M n) σ with hgdef
  set aL : LL p M n := ⟨a, haL⟩ with haLdef
  have hcoe_g : ∀ z : LL p M n, ((g z : LL p M n) : Ω) = σ z := fun z => coe_res p (LL p M n) σ z
  have hgH : g ∈ HS p M n := by
    rw [mem_HS_iff, mem_T_iff' p le_rfl]
    intro z hz
    apply Subtype.ext
    rw [hcoe_g]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hz
  have hga : g aL ≠ aL := fun h => hne (by rw [← hcoe_g aL, h])
  set Sa : Subgroup G' := MulAction.stabilizer G' aL with hSadef
  have hmemSa : ∀ {s : G'}, s ∈ Sa ↔ s aL = aL := fun {s} => by
    rw [hSadef, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  have hSaH : ∀ s ∈ Sa, s ∈ HS p M n := by
    intro s hs
    rw [hmemSa] at hs
    have hsa : lift p (LL p M n) s a = a := by
      rw [show a = ((aL : LL p M n) : Ω) from rfl, lift_coe, hs]
    rw [mem_HS_iff, mem_T_iff]
    intro z hz
    exact apply_eq_of_mem_adjoin_simple _ hsa (hQa hz)

  have hhyp : ∀ c : LL p M n, ‖(c : Ω)‖ ≤ 1 → (∀ s ∈ Sa, s c = c) →
      ‖((g c : LL p M n) : Ω) - c‖ ≤ ‖((g aL : LL p M n) : Ω) - aL‖ := by
    intro c hc hcS
    set Ka : IntermediateField ℚ_[p] (LL p M n) := IntermediateField.adjoin ℚ_[p] {aL} with hKa
    have hcfix : c ∈ IntermediateField.fixedField Ka.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro s hs
      refine hcS s ((hmemSa).mpr ?_)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs aL
        (IntermediateField.mem_adjoin_simple_self ℚ_[p] aL)
    rw [IsGalois.fixedField_fixingSubgroup] at hcfix
    have hcΩ : (c : Ω) ∈ IntermediateField.adjoin ℚ_[p] {a} := by
      have h1 : (c : Ω) ∈ IntermediateField.lift Ka := (IntermediateField.mem_lift c).mpr hcfix
      rwa [hKa, IntermediateField.lift_adjoin, Set.image_singleton] at h1
    obtain ⟨P, hP, hPc⟩ := hgen _ hcΩ hc
    have hga1 : ‖((g aL : LL p M n) : Ω)‖ ≤ 1 := by rw [norm_coe_apply]; exact ha1
    have h1 : ((g c : LL p M n) : Ω) = aeval ((g aL : LL p M n) : Ω) P := by
      rw [← lift_coe, ← lift_coe, show ((aL : LL p M n) : Ω) = a from rfl, aeval_algHom_apply, hPc]
    rw [h1, show ((c : LL p M n) : Ω) = aeval a P from hPc.symm]
    exact norm_aeval_sub_aeval_le p hP hga1 ha1
  have hprod : ∏ s ∈ fs p Sa, D p x (g * s) ≤ ‖((g aL : LL p M n) : Ω) - aL‖ :=
    prod_D_le_norm_apply_sub p hx Sa aL g hhyp

  have hfac : ∀ s ∈ fs p Sa, r₀ < D p x (g * s) := by
    intro s hs
    have hs' : s ∈ Sa := (mem_fs p).mp hs
    refine hN₀ n hn x hx (g * s) ((HS p M n).mul_mem hgH (hSaH s hs')) fun hgs => hga ?_
    have hg' : g = s⁻¹ := eq_inv_of_mul_eq_one_left hgs
    rw [hg']
    exact (hmemSa).mp (Sa.inv_mem hs')
  have hlt : r₀ ^ (fs p Sa).card < ∏ s ∈ fs p Sa, D p x (g * s) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty (fun _ _ => hr₀pos) hfac ⟨1, (mem_fs p).mpr Sa.one_mem⟩
  have hcard : (fs p Sa).card ≤ d := by
    refine le_trans (Finset.card_le_card fun s hs => ?_) (card_T_n_le p hy)
    rw [← fs_HS, mem_fs]
    exact hSaH s ((mem_fs p).mp hs)
  calc (p : ℝ) ^ (-ε) = r₀ ^ d := hr₀d.symm
    _ ≤ r₀ ^ (fs p Sa).card := pow_le_pow_of_le_one hr₀pos.le hr₀1 hcard
    _ < ∏ s ∈ fs p Sa, D p x (g * s) := hlt
    _ ≤ ‖((g aL : LL p M n) : Ω) - aL‖ := hprod
    _ = ‖σ a - a‖ := by rw [hcoe_g]

end Final

end TTA
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower.TTA"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower.TTA"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    [Normal ℚ_[p] M] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : PadicAlgCl p,
      a ∈ M ⊔ PadicAlgCl.cyclotomicTower p n → ‖a‖ ≤ 1 →
      PadicAlgCl.cyclotomicTower p n ≤ IntermediateField.adjoin ℚ_[p] {a} →
      (∀ c ∈ IntermediateField.adjoin ℚ_[p] {a}, ‖c‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval a P = c) →
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup → σ a ≠ a →
        (p : ℝ) ^ (-ε) < ‖σ a - a‖ :=
  TTA.main p M ε hε

end S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower (solution)
