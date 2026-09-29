-- Prove2me | solution 1 for PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7e37081a-6de1-5cfe-ab90-26573d952080

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Complex Filter Set
p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.PeriodPair Topology"

namespace PeriodPair
p2m_export "PeriodPair" "ω₁_mem_lattice analyticAt_weierstrassPExcept isClosed_lattice lattice weierstrassP_add_coe lattice_eq_span_range_basis ω₁ mk differentiableOn_weierstrassP weierstrassP_sub_coe weierstrassPExcept_add deriv_weierstrassP ω₂ derivWeierstrassP derivWeierstrassP_add_coe weierstrassP mem_lattice indep ω₂_mem_lattice weierstrassCurve DiscriminantNeZero toPoint toPoint_of_mem toPoint_of_notMem scale scale_ω₁ scale_ω₂ isUniformization_toPoint discriminant_ne_zero"
namespace MulToRat
p2m_open "PeriodPair"

theorem omega1_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

theorem intCast_mul_mem_lattice (L : PeriodPair) (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    (n : ℂ) * z ∈ L.lattice := by
  rw [← zsmul_eq_mul]; exact L.lattice.smul_mem n hz

theorem mem_scale_lattice_iff (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    z ∈ (L.scale α).lattice ↔ ∃ w ∈ L.lattice, z = α * w := by
  constructor
  · intro hz
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hz
    refine ⟨m * L.ω₁ + n * L.ω₂, PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩, ?_⟩
    simp only [scale_ω₁, scale_ω₂]; ring
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
    refine PeriodPair.mem_lattice.mpr ⟨m, n, ?_⟩
    simp only [scale_ω₁, scale_ω₂]; ring

theorem mul_mem_scale_lattice (L : PeriodPair) (α : ℂˣ) {w : ℂ} (hw : w ∈ L.lattice) :
    (α : ℂ) * w ∈ (L.scale α).lattice :=
  (mem_scale_lattice_iff L α _).mpr ⟨w, hw, rfl⟩

noncomputable def scaleEquiv (L : PeriodPair) (α : ℂˣ) : L.lattice ≃ (L.scale α).lattice where
  toFun l := ⟨α * l, mul_mem_scale_lattice L α l.2⟩
  invFun l := ⟨α⁻¹ * l, by
    obtain ⟨w, hw, h⟩ := (mem_scale_lattice_iff L α l).mp l.2
    rw [h, ← mul_assoc, Units.inv_mul, one_mul]; exact hw⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

@[scoped simp] theorem coe_scaleEquiv (L : PeriodPair) (α : ℂˣ) (l : L.lattice) :
    ((scaleEquiv L α l : (L.scale α).lattice) : ℂ) = α * l := rfl

theorem weierstrassP_scale (L : PeriodPair) (α : ℂˣ) (w : ℂ) :
    ℘[L.scale α] w = (α : ℂ)⁻¹ ^ 2 * ℘[L] ((α : ℂ)⁻¹ * w) := by
  simp only [weierstrassP]
  rw [← (scaleEquiv L α).tsum_eq, ← tsum_mul_left]
  congr 1 with l
  simp only [coe_scaleEquiv]
  have hα : (α : ℂ) ≠ 0 := α.ne_zero
  have e1 : w - α * l = α * ((α : ℂ)⁻¹ * w - l) := by field_simp
  rw [e1, mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, ← inv_pow, mul_sub]

theorem derivWeierstrassP_scale (L : PeriodPair) (α : ℂˣ) (w : ℂ) :
    ℘'[L.scale α] w = (α : ℂ)⁻¹ ^ 3 * ℘'[L] ((α : ℂ)⁻¹ * w) := by
  simp only [derivWeierstrassP]
  rw [← (scaleEquiv L α).tsum_eq, mul_neg, ← tsum_mul_left]
  congr 2 with l
  simp only [coe_scaleEquiv]
  have hα : (α : ℂ) ≠ 0 := α.ne_zero
  have e1 : w - α * l = α * ((α : ℂ)⁻¹ * w - l) := by field_simp
  rw [e1, mul_pow]
  generalize ((α : ℂ)⁻¹ * w - l) ^ 3 = D
  rw [inv_pow, mul_comm ((α : ℂ) ^ 3) D, ← div_div, div_eq_mul_inv _ ((α : ℂ) ^ 3), mul_comm]

theorem weierstrassP_mul_eq (L' : PeriodPair) (a : ℂˣ) (z : ℂ) :
    ℘[L'] (a * z) = (a : ℂ)⁻¹ ^ 2 * ℘[L'.scale a⁻¹] z := by
  have h := weierstrassP_scale L' a⁻¹ z
  rw [h]
  simp only [Units.val_inv_eq_inv_val, inv_inv]
  have hα : (a : ℂ) ≠ 0 := a.ne_zero
  field_simp

theorem derivWeierstrassP_mul_eq (L' : PeriodPair) (a : ℂˣ) (z : ℂ) :
    ℘'[L'] (a * z) = (a : ℂ)⁻¹ ^ 3 * ℘'[L'.scale a⁻¹] z := by
  have h := derivWeierstrassP_scale L' a⁻¹ z
  rw [h]
  simp only [Units.val_inv_eq_inv_val, inv_inv]
  have hα : (a : ℂ) ≠ 0 := a.ne_zero
  field_simp

theorem sub_fract_mem_lattice (L : PeriodPair) (z : ℂ) :
    z - ZSpan.fract L.basis z ∈ L.lattice := by
  rw [L.lattice_eq_span_range_basis]
  have h := (ZSpan.fract_eq_fract L.basis (ZSpan.fract L.basis z) z).mp
    (by rw [ZSpan.fract_eq_self.mpr (ZSpan.fract_mem_fundamentalDomain L.basis z)])
  simpa [neg_add_eq_sub] using h

theorem apply_eq_apply_of_differentiable_of_forall_periodic (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ l ∈ L.lattice, ∀ z, f (z + l) = f z) (z w : ℂ) :
    f z = f w := by
  apply hf.apply_eq_apply_of_bounded
  have hrange : range f ⊆ f '' closure (ZSpan.fundamentalDomain L.basis) := by
    rintro - ⟨u, rfl⟩
    refine ⟨ZSpan.fract L.basis u, subset_closure (ZSpan.fract_mem_fundamentalDomain _ u), ?_⟩
    have h := hper _ (sub_fract_mem_lattice L u) (ZSpan.fract L.basis u)
    rw [add_sub_cancel] at h
    exact h.symm
  refine Bornology.IsBounded.subset ?_ hrange
  refine (IsCompact.image ?_ hf.continuous).isBounded
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (ZSpan.fundamentalDomain_isBounded L.basis).closure

section Coset

variable (L M : PeriodPair)

abbrev Q := M.lattice.toAddSubgroup ⧸ L.lattice.toAddSubgroup.addSubgroupOf M.lattice.toAddSubgroup

theorem finite_Q (hLM : L.lattice ≤ M.lattice) : Finite (Q L M) := by

  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hLM L.ω₁_mem_lattice)
  obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp (hLM L.ω₂_mem_lattice)
  have h₁ : ((a * d - b * c : ℤ) : ℂ) * M.ω₁ = d * L.ω₁ - b * L.ω₂ := by
    push_cast; linear_combination d * hab - b * hcd
  have h₂ : ((a * d - b * c : ℤ) : ℂ) * M.ω₂ = a * L.ω₂ - c * L.ω₁ := by
    push_cast; linear_combination a * hcd - c * hab
  have hdet : a * d - b * c ≠ 0 := by
    intro h0
    rw [h0] at h₁ h₂
    push_cast at h₁ h₂
    rw [zero_mul] at h₁ h₂
    have i1 := LinearIndependent.pair_iff.mp L.indep (d : ℝ) (-b : ℝ) (by
      simp only [Complex.real_smul, Complex.ofReal_intCast, Complex.ofReal_neg]
      linear_combination -h₁)
    have i2 := LinearIndependent.pair_iff.mp L.indep (-c : ℝ) (a : ℝ) (by
      simp only [Complex.real_smul, Complex.ofReal_intCast, Complex.ofReal_neg]
      linear_combination -h₂)
    have ha : a = 0 := by exact_mod_cast i2.2
    have hb : b = 0 := by have := i1.2; simp at this; exact_mod_cast this
    rw [ha, hb] at hab
    simp at hab
    exact omega1_ne_zero L hab.symm
  set N : ℕ := (a * d - b * c).natAbs with hN
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.mpr hdet
  have hmul : ∀ m ∈ M.lattice, ((a * d - b * c : ℤ) : ℂ) * m ∈ L.lattice := by
    intro m hm
    obtain ⟨p, r, rfl⟩ := PeriodPair.mem_lattice.mp hm
    have : ((a * d - b * c : ℤ) : ℂ) * (p * M.ω₁ + r * M.ω₂) =
        ((p * d - r * c : ℤ) : ℂ) * L.ω₁ + ((r * a - p * b : ℤ) : ℂ) * L.ω₂ := by
      have e : ((a * d - b * c : ℤ) : ℂ) * (p * M.ω₁ + r * M.ω₂) =
          p * (((a * d - b * c : ℤ) : ℂ) * M.ω₁) + r * (((a * d - b * c : ℤ) : ℂ) * M.ω₂) := by ring
      rw [e, h₁, h₂]; push_cast; ring
    rw [this]
    exact PeriodPair.mem_lattice.mpr ⟨_, _, rfl⟩
  have hNmul : ∀ m ∈ M.lattice, (N : ℂ) * m ∈ L.lattice := by
    intro m hm
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_cast
    rcases Int.natAbs_eq (a * d - b * c) with h | h
    · have h' : ((N : ℤ) : ℂ) = ((a * d - b * c : ℤ) : ℂ) := by rw [hN]; exact_mod_cast h.symm
      rw [hcast, h']; exact hmul m hm
    · have h' : ((N : ℤ) : ℂ) = -((a * d - b * c : ℤ) : ℂ) := by
        have h2 : ((N : ℤ)) = -(a * d - b * c) := by rw [hN]; omega
        rw [h2]; push_cast; ring
      rw [hcast, h', neg_mul]; exact L.lattice.neg_mem (hmul m hm)

  haveI : AddGroup.FG M.lattice.toAddSubgroup :=
    Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ M.lattice)
  haveI hfi := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg M.lattice.toAddSubgroup hN0
  have hle : (nsmulAddMonoidHom N : M.lattice.toAddSubgroup →+ M.lattice.toAddSubgroup).range ≤
      L.lattice.toAddSubgroup.addSubgroupOf M.lattice.toAddSubgroup := by
    rintro x ⟨y, rfl⟩
    simp only [AddSubgroup.mem_addSubgroupOf, nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    have : ((N • y : M.lattice.toAddSubgroup) : ℂ) = (N : ℂ) * (y : ℂ) := by
      simp [nsmul_eq_mul]
    rw [this]
    exact hNmul _ y.2
  haveI := AddSubgroup.finiteIndex_of_le hle
  exact AddSubgroup.finite_quotient_of_finiteIndex

variable {L M}

noncomputable def rep (q : Q L M) : ℂ := ((Quotient.out q : M.lattice.toAddSubgroup) : ℂ)

theorem rep_mem (q : Q L M) : rep q ∈ M.lattice := (Quotient.out q : M.lattice.toAddSubgroup).2

theorem mk_out (q : Q L M) : (QuotientAddGroup.mk (Quotient.out q) : Q L M) = q :=
  QuotientAddGroup.out_eq' q

theorem mk_eq_mk_iff (m m' : M.lattice.toAddSubgroup) :
    (QuotientAddGroup.mk m : Q L M) = QuotientAddGroup.mk m' ↔ (m' : ℂ) - m ∈ L.lattice := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [neg_add_eq_sub]

theorem sub_rep_mk_mem (m : M.lattice.toAddSubgroup) :
    (m : ℂ) - rep (QuotientAddGroup.mk m : Q L M) ∈ L.lattice := by
  have h := (mk_eq_mk_iff (Quotient.out (QuotientAddGroup.mk m : Q L M)) m).mp
    (by rw [mk_out])
  exact h

theorem rep_sub_rep_notMem {q q' : Q L M} (hq : q ≠ q') : rep q' - rep q ∉ L.lattice := by
  intro h
  apply hq
  rw [← mk_out q, ← mk_out q']
  exact (mk_eq_mk_iff _ _).mpr h

variable (L M) in

noncomputable def negClass (μ : ℂ) (hμ : μ ∈ M.lattice) : Q L M :=
  QuotientAddGroup.mk (⟨-μ, M.lattice.neg_mem hμ⟩ : M.lattice.toAddSubgroup)

theorem add_rep_negClass_mem (μ : ℂ) (hμ : μ ∈ M.lattice) :
    μ + rep (negClass L M μ hμ) ∈ L.lattice := by
  have h := sub_rep_mk_mem (L := L) (⟨-μ, M.lattice.neg_mem hμ⟩ : M.lattice.toAddSubgroup)
  have : μ + rep (negClass L M μ hμ) = -((-μ : ℂ) - rep (negClass L M μ hμ)) := by ring
  rw [this]
  exact L.lattice.neg_mem h

theorem add_rep_notMem_of_ne {μ : ℂ} (hμ : μ ∈ M.lattice) {q : Q L M} (hq : q ≠ negClass L M μ hμ) :
    μ + rep q ∉ L.lattice := by
  intro h
  apply rep_sub_rep_notMem hq
  have : rep (negClass L M μ hμ) - rep q = (μ + rep (negClass L M μ hμ)) - (μ + rep q) := by ring
  rw [this]
  exact L.lattice.sub_mem (add_rep_negClass_mem μ hμ) h

theorem coset_identity (hLM : L.lattice ≤ M.lattice) [Fintype (Q L M)] :
    ∃ K : ℂ, ∀ z : ℂ, ℘[M] z = ∑ q : Q L M, ℘[L] (z + rep q) + K := by
  classical
  set g : ℂ → ℂ := fun z => ℘[M] z - ∑ q : Q L M, ℘[L] (z + rep q) with hg

  have hper : ∀ l ∈ L.lattice, ∀ z, g (z + l) = g z := by
    intro l hl z
    simp only [hg]
    have h1 : ℘[M] (z + l) = ℘[M] z := M.weierstrassP_add_coe z ⟨l, hLM hl⟩
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have : z + l + rep q = (z + rep q) + l := by ring
    rw [this]
    exact L.weierstrassP_add_coe (z + rep q) ⟨l, hl⟩

  have hdiff : Differentiable ℂ g := by
    intro μ
    by_cases hμ : μ ∈ M.lattice
    ·
      set q₀ := negClass L M μ hμ with hq₀
      set w₀ : ℂ := μ + rep q₀ with hw₀
      have hw₀L : w₀ ∈ L.lattice := add_rep_negClass_mem μ hμ
      have hgeq : g = fun z => ℘[M - μ] z - ℘[L - w₀] (z + rep q₀)
          - ∑ q ∈ Finset.univ.erase q₀, ℘[L] (z + rep q) + (1 / w₀ ^ 2 - 1 / μ ^ 2) := by
        funext z
        simp only [hg]
        rw [← M.weierstrassPExcept_add ⟨μ, hμ⟩ z, ← Finset.add_sum_erase _ _ (Finset.mem_univ q₀),
          ← L.weierstrassPExcept_add ⟨w₀, hw₀L⟩ (z + rep q₀)]
        have : z + rep q₀ - w₀ = z - μ := by rw [hw₀]; ring
        simp only [this]
        ring
      rw [hgeq]
      refine ((DifferentiableAt.sub (DifferentiableAt.sub ?_ ?_) ?_).add (differentiableAt_const _))
      · exact (M.analyticAt_weierstrassPExcept μ).differentiableAt
      · have ha : AnalyticAt ℂ ℘[L - w₀] (μ + rep q₀) := L.analyticAt_weierstrassPExcept w₀
        exact ha.differentiableAt.comp μ ((differentiableAt_id).add (differentiableAt_const _))
      · refine DifferentiableAt.fun_sum fun q hq => ?_
        have hq' : q ≠ q₀ := (Finset.mem_erase.mp hq).1
        have hnot : μ + rep q ∉ L.lattice := add_rep_notMem_of_ne hμ hq'
        have hd : DifferentiableAt ℂ ℘[L] (μ + rep q) :=
          L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hnot)
        exact hd.comp μ ((differentiableAt_id).add (differentiableAt_const _))
    ·
      refine DifferentiableAt.sub ?_ ?_
      · exact M.differentiableOn_weierstrassP.differentiableAt (M.isClosed_lattice.isOpen_compl.mem_nhds hμ)
      · refine DifferentiableAt.fun_sum fun q _ => ?_
        have hnot : μ + rep q ∉ L.lattice := fun h => hμ (by
          have : μ = (μ + rep q) - rep q := by ring
          rw [this]
          exact M.lattice.sub_mem (hLM h) (rep_mem q))
        have hd : DifferentiableAt ℂ ℘[L] (μ + rep q) :=
          L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hnot)
        exact hd.comp μ ((differentiableAt_id).add (differentiableAt_const _))
  refine ⟨g 0, fun z => ?_⟩
  have := apply_eq_apply_of_differentiable_of_forall_periodic L hdiff hper z 0
  simp only [hg] at this ⊢
  linear_combination this

theorem deriv_coset_identity (hLM : L.lattice ≤ M.lattice) [Fintype (Q L M)] {K : ℂ}
    (hK : ∀ z : ℂ, ℘[M] z = ∑ q : Q L M, ℘[L] (z + rep q) + K) {z : ℂ} (hz : z ∉ M.lattice) :
    ℘'[M] z = ∑ q : Q L M, ℘'[L] (z + rep q) := by
  have hfun : ℘[M] = fun z => ∑ q : Q L M, ℘[L] (z + rep q) + K := funext hK
  have h := congrArg (fun f => deriv f z) hfun
  simp only [M.deriv_weierstrassP] at h
  rw [h, deriv_add_const]
  have hd : ∀ q : Q L M, DifferentiableAt ℂ (fun z => ℘[L] (z + rep q)) z := by
    intro q
    have hnot : z + rep q ∉ L.lattice := fun h' => hz (by
      have : z = (z + rep q) - rep q := by ring
      rw [this]
      exact M.lattice.sub_mem (hLM h') (rep_mem q))
    have hdq : DifferentiableAt ℂ ℘[L] (z + rep q) :=
      L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hnot)
    exact hdq.comp z ((differentiableAt_id).add (differentiableAt_const _))
  have : (fun z => ∑ q : Q L M, ℘[L] (z + rep q)) = ∑ q : Q L M, fun z => ℘[L] (z + rep q) := by
    funext z; simp [Finset.sum_apply]
  rw [this, deriv_sum fun q _ => hd q]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [deriv_comp_add_const, L.deriv_weierstrassP]

end Coset

section IsRat

open Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

@[scoped simp] theorem bc_CX (x y : k) : bc x y (C X : F[X][Y]) = x := by
  simp [bc]

@[scoped simp] theorem bc_Y (x y : k) : bc x y (Y : F[X][Y]) = y := by
  simp [bc]

variable (W : WeierstrassCurve F)

def IsRat (f : k → k → k) : Prop :=
  ∃ (n d : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B →
      bc x y d ≠ 0 ∧ f x y = bc x y n / bc x y d

namespace IsRat

variable {W}
variable {f g : k → k → k}

theorem of_eq (hf : IsRat W f) (hfg : ∀ x y, g x y = f x y) : IsRat W g := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  exact ⟨n, d, B, hB, fun x y hxy hx => by rw [hfg]; exact h x y hxy hx⟩

theorem poly (p : F[X][Y]) : IsRat W (fun (x y : k) => bc x y p) :=
  ⟨p, 1, ∅, Set.finite_empty, fun x y _ _ => by simp⟩

theorem const (a : F) : IsRat W (fun (_ _ : k) => algebraMap F k a) :=
  (poly (C (C a))).of_eq fun x y => by simp

theorem fst : IsRat W (fun (x : k) (_ : k) => x) :=
  (poly (C X)).of_eq fun x y => by simp

theorem snd : IsRat W (fun (_ : k) (y : k) => y) :=
  (poly Y).of_eq fun x y => by simp

theorem add (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y + g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_add, map_mul, map_mul, map_mul, div_add_div _ _ hd₁ hd₂]
  ring

theorem neg (hf : IsRat W f) : IsRat W (fun x y => -f x y) := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  refine ⟨-n, d, B, hB, fun x y hxy hx => ?_⟩
  obtain ⟨hd, hf⟩ := h x y hxy hx
  exact ⟨hd, by beta_reduce; rw [hf, map_neg, neg_div]⟩

theorem sub (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y - g x y) :=
  (hf.add hg.neg).of_eq fun x y => by ring

theorem mul (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y * g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * n₂, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_mul, map_mul, div_mul_div_comm]

theorem div (hf : IsRat W f) (hg : IsRat W g) {B₀ : Set k} (hB₀ : B₀.Finite)
    (hg0 : ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B₀ → g x y ≠ 0) :
    IsRat W (fun x y => f x y / g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * d₂, d₁ * n₂, B₀ ∪ B₁ ∪ B₂, (hB₀.union hB₁).union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1.2
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  have hg' := hg0 x y hxy hx.1.1
  have hn₂ : bc x y n₂ ≠ 0 := by
    intro h0; apply hg'; rw [hf₂, h0, zero_div]
  refine ⟨by rw [map_mul]; exact mul_ne_zero hd₁ hn₂, ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_mul, map_mul, div_div_div_eq]

theorem sum {ι : Type*} (s : Finset ι) (h : ι → k → k → k) (hh : ∀ i ∈ s, IsRat W (h i)) :
    IsRat W (fun x y => ∑ i ∈ s, h i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const (W := W) (k := k) 0).of_eq fun x y => by simp
  | insert i s hi ih =>
    have := (hh i (Finset.mem_insert_self i s)).add (ih fun j hj => hh j (Finset.mem_insert_of_mem hj))
    exact this.of_eq fun x y => by rw [Finset.sum_insert hi]

theorem ite (P : Prop) [Decidable P] (hf : IsRat W f) (hg : IsRat W g) :
    IsRat W (fun x y => if P then f x y else g x y) := by
  by_cases hP : P
  · exact hf.of_eq fun x y => by rw [if_pos hP]
  · exact hg.of_eq fun x y => by rw [if_neg hP]

end IsRat

variable {W}

theorem exists_some_of_eq {W₂ : WeierstrassCurve F} {Q : (W₂.baseChange k).toAffine.Point} {x₁ y₁ : k}
    {h₁ : (W₂.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

variable [DecidableEq k]

theorem isRationallyRepresented_of_isRat {W₁ W₂ : WeierstrassCurve F}
    (γ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point) {fX fY : k → k → k}
    (hX : IsRat W₁ fX) (hY : IsRat W₁ fY) {B₀ : Set k} (hB₀ : B₀.Finite)
    (hγ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B₀ →
      ∃ h', γ (.some x y h) = .some (fX x y) (fY x y) h') :
    WeierstrassCurve.IsRationallyRepresented k W₁ W₂ γ := by
  obtain ⟨nX, dX, BX, hBX, hX⟩ := hX
  obtain ⟨nY, dY, BY, hBY, hY⟩ := hY
  refine ⟨nX, dX, nY, dY, B₀ ∪ BX ∪ BY, (hB₀.union hBX).union hBY, fun x y h hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hdX, hfX⟩ := hX x y h hx.1.2
  obtain ⟨hdY, hfY⟩ := hY x y h hx.2
  obtain ⟨h', hγ'⟩ := hγ x y h hx.1.1
  refine ⟨hdX, hdY, ?_⟩
  simp only [evalEvalBC_eq]
  exact exists_some_of_eq hγ' hfX hfY

end IsRat

section Chord

variable (L : PeriodPair) (hL : L.DiscriminantNeZero)

noncomputable def T : ℂ →+ L.weierstrassCurve.toAffine.Point :=
  AddMonoidHom.mk' (L.toPoint hL) (PeriodPair.isUniformization_toPoint L hL).1

theorem T_apply (z : ℂ) : T L hL z = L.toPoint hL z := rfl

theorem T_surjective : Function.Surjective (T L hL) :=
  (PeriodPair.isUniformization_toPoint L hL).2.1

theorem T_eq_zero_iff {z : ℂ} : T L hL z = 0 ↔ z ∈ L.lattice :=
  ⟨(PeriodPair.isUniformization_toPoint L hL).2.2 z, fun h => L.toPoint_of_mem hL h⟩

theorem T_ker : (T L hL).ker = L.lattice.toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker, T_eq_zero_iff]
  rfl

variable {hL}

theorem add_notMem_of_weierstrassP_ne {z c : ℂ} (hz : z ∉ L.lattice) (hc : c ∉ L.lattice)
    (hx : ℘[L] z ≠ ℘[L] c) : z + c ∉ L.lattice := by
  intro hzc
  have hL := PeriodPair.discriminant_ne_zero L
  have h := (PeriodPair.isUniformization_toPoint L hL).1 z c
  rw [L.toPoint_of_mem hL hzc, L.toPoint_of_notMem hL hz, L.toPoint_of_notMem hL hc] at h
  have h' := (eq_neg_of_add_eq_zero_left h.symm)
  rw [WeierstrassCurve.Affine.Point.neg_some] at h'
  exact hx (WeierstrassCurve.Affine.Point.some.inj h').1

theorem weierstrassP_add_eq {z c : ℂ} (hz : z ∉ L.lattice) (hc : c ∉ L.lattice)
    (hx : ℘[L] z ≠ ℘[L] c) :
    ℘[L] (z + c) = L.weierstrassCurve.toAffine.addX (℘[L] z) (℘[L] c)
        (L.weierstrassCurve.toAffine.slope (℘[L] z) (℘[L] c) (℘'[L] z / 2) (℘'[L] c / 2)) ∧
      ℘'[L] (z + c) / 2 = L.weierstrassCurve.toAffine.addY (℘[L] z) (℘[L] c) (℘'[L] z / 2)
        (L.weierstrassCurve.toAffine.slope (℘[L] z) (℘[L] c) (℘'[L] z / 2) (℘'[L] c / 2)) := by
  have hzc : z + c ∉ L.lattice := add_notMem_of_weierstrassP_ne L hz hc hx
  have hL := PeriodPair.discriminant_ne_zero L
  have h := (PeriodPair.isUniformization_toPoint L hL).1 z c
  rw [L.toPoint_of_notMem hL hzc, L.toPoint_of_notMem hL hz, L.toPoint_of_notMem hL hc,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx] at h
  obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj h
  exact ⟨h1, h2⟩

noncomputable def chordX (xc yc : ℂ) (x y : ℂ) : ℂ := ((y - yc) / (x - xc)) ^ 2 - x - xc

noncomputable def chordY (xc yc : ℂ) (x y : ℂ) : ℂ :=
  -(((y - yc) / (x - xc)) * (chordX xc yc x y - x) + y)

theorem addX_eq_chordX {x xc y yc : ℂ} (hx : x ≠ xc) :
    L.weierstrassCurve.toAffine.addX x xc (L.weierstrassCurve.toAffine.slope x xc y yc) =
      chordX xc yc x y := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp [WeierstrassCurve.Affine.addX, chordX]

theorem addY_eq_chordY {x xc y yc : ℂ} (hx : x ≠ xc) :
    L.weierstrassCurve.toAffine.addY x xc y (L.weierstrassCurve.toAffine.slope x xc y yc) =
      chordY xc yc x y := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX, chordY, chordX]

theorem isRat_chordX (xc yc : ℂ) : IsRat (k := ℂ) L.weierstrassCurve (chordX xc yc) := by
  have hsl : IsRat (k := ℂ) L.weierstrassCurve (fun x y : ℂ => (y - yc) / (x - xc)) := by
    refine (IsRat.snd.sub (IsRat.const yc)).div (IsRat.fst.sub (IsRat.const xc))
      (Set.finite_singleton xc) fun x y _ hx => ?_
    simpa [sub_eq_zero] using hx
  exact (((hsl.mul hsl).sub IsRat.fst).sub (IsRat.const xc)).of_eq fun x y => by
    simp only [chordX, sq, Algebra.algebraMap_self, RingHom.id_apply]

theorem isRat_chordY (xc yc : ℂ) : IsRat (k := ℂ) L.weierstrassCurve (chordY xc yc) := by
  have hsl : IsRat (k := ℂ) L.weierstrassCurve (fun x y : ℂ => (y - yc) / (x - xc)) := by
    refine (IsRat.snd.sub (IsRat.const yc)).div (IsRat.fst.sub (IsRat.const xc))
      (Set.finite_singleton xc) fun x y _ hx => ?_
    simpa [sub_eq_zero] using hx
  exact ((hsl.mul ((isRat_chordX L xc yc).sub IsRat.fst)).add IsRat.snd).neg.of_eq fun x y => rfl

end Chord

section Main

variable (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)

noncomputable def mulHom (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) :
    L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point :=
  (QuotientAddGroup.lift (T L hL).ker ((T L' hL').comp (AddMonoidHom.mulLeft a)) (by
      intro z hz
      rw [T_ker] at hz
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, T_eq_zero_iff]
      exact ha z hz)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (T L hL) (T_surjective L hL)).symm.toAddMonoidHom

theorem mulHom_apply_T (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) (z : ℂ) :
    mulHom L L' hL hL' a ha (T L hL z) = T L' hL' (a * z) := by
  set e := QuotientAddGroup.quotientKerEquivOfSurjective (T L hL) (T_surjective L hL) with he_def
  have he : e (QuotientAddGroup.mk z) = T L hL z := QuotientAddGroup.kerLift_mk (T L hL) z
  have he' : e.symm (T L hL z) = QuotientAddGroup.mk z := e.symm_apply_eq.mpr he.symm
  simp only [mulHom]
  rw [AddMonoidHom.comp_apply]
  change (QuotientAddGroup.lift (T L hL).ker ((T L' hL').comp (AddMonoidHom.mulLeft a)) _)
    (e.symm (T L hL z)) = _
  rw [he', QuotientAddGroup.lift_mk]
  rfl

theorem mulHom_apply_toPoint (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) (z : ℂ) :
    mulHom L L' hL hL' a ha (L.toPoint hL z) = L'.toPoint hL' (a * z) :=
  mulHom_apply_T L L' hL hL' a ha z

theorem exists_mem_rationalHomSet (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) :
    ∃ β ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve,
      ∀ z : ℂ, β (L.toPoint hL z) = L'.toPoint hL' (a * z) := by
  classical
  refine ⟨mulHom L L' hL hL' a ha, ?_, mulHom_apply_toPoint L L' hL hL' a ha⟩
  by_cases ha0 : a = 0
  ·
    left
    ext P
    obtain ⟨z, rfl⟩ := T_surjective L hL P
    rw [mulHom_apply_T, ha0, zero_mul, map_zero]
    rfl
  right
  set au : ℂˣ := Units.mk0 a ha0 with hau
  set M : PeriodPair := L'.scale au⁻¹ with hM
  have hLM : L.lattice ≤ M.lattice := by
    intro l hl
    rw [hM, mem_scale_lattice_iff]
    refine ⟨a * l, ha l hl, ?_⟩
    simp [hau, ha0]
  haveI : Fintype (Q L M) := @Fintype.ofFinite _ (finite_Q L M hLM)
  obtain ⟨K, hK⟩ := coset_identity (L := L) (M := M) hLM

  set xq : Q L M → ℂ := fun q => ℘[L] (rep q) with hxq
  set yq : Q L M → ℂ := fun q => ℘'[L] (rep q) / 2 with hyq
  set fXq : Q L M → ℂ → ℂ → ℂ := fun q x y =>
    if rep q ∈ L.lattice then x else chordX (xq q) (yq q) x y with hfXq
  set fYq : Q L M → ℂ → ℂ → ℂ := fun q x y =>
    if rep q ∈ L.lattice then y else chordY (xq q) (yq q) x y with hfYq
  set FX : ℂ → ℂ → ℂ := fun x y => (a⁻¹) ^ 2 * (∑ q, fXq q x y + K) with hFX
  set FY : ℂ → ℂ → ℂ := fun x y => (a⁻¹) ^ 3 * ∑ q, fYq q x y with hFY
  have hFXr : IsRat (k := ℂ) L.weierstrassCurve FX :=
    ((IsRat.const ((a⁻¹) ^ 2)).mul ((IsRat.sum (W := L.weierstrassCurve) Finset.univ fXq
      fun q _ => IsRat.ite _ IsRat.fst (isRat_chordX L _ _)).add (IsRat.const K))).of_eq
      fun x y => by simp only [hFX, Algebra.algebraMap_self, RingHom.id_apply]
  have hFYr : IsRat (k := ℂ) L.weierstrassCurve FY :=
    ((IsRat.const ((a⁻¹) ^ 3)).mul (IsRat.sum (W := L.weierstrassCurve) Finset.univ fYq
      fun q _ => IsRat.ite _ IsRat.snd (isRat_chordY L _ _))).of_eq
      fun x y => by simp only [hFY, Algebra.algebraMap_self, RingHom.id_apply]
  set B : Set ℂ := Set.range xq with hB
  have hBfin : B.Finite := Set.finite_range xq
  refine isRationallyRepresented_of_isRat (F := ℂ) (k := ℂ) (W₁ := L.weierstrassCurve)
    (W₂ := L'.weierstrassCurve) (mulHom L L' hL hL' a ha) hFXr hFYr hBfin ?_
  intro x y h hxB

  obtain ⟨z, hz⟩ := T_surjective L hL (.some x y h)
  have hzL : z ∉ L.lattice := by
    intro hmem
    rw [T_apply, L.toPoint_of_mem hL hmem] at hz
    cases hz
  have hxz : ℘[L] z = x ∧ ℘'[L] z / 2 = y := by
    rw [T_apply, L.toPoint_of_notMem hL hzL] at hz
    obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hz
    exact ⟨h1, h2⟩

  have hzM : z ∉ M.lattice := by
    intro hzM
    apply hxB
    have hsub : z - rep (QuotientAddGroup.mk (⟨z, hzM⟩ : M.lattice.toAddSubgroup) : Q L M) ∈ L.lattice :=
      sub_rep_mk_mem (L := L) (⟨z, hzM⟩ : M.lattice.toAddSubgroup)
    refine ⟨QuotientAddGroup.mk (⟨z, hzM⟩ : M.lattice.toAddSubgroup), ?_⟩
    simp only [hxq]
    rw [← hxz.1]
    have e : rep (QuotientAddGroup.mk (⟨z, hzM⟩ : M.lattice.toAddSubgroup) : Q L M) =
        z - (z - rep (QuotientAddGroup.mk (⟨z, hzM⟩ : M.lattice.toAddSubgroup) : Q L M)) := by ring
    rw [e]
    exact L.weierstrassP_sub_coe z ⟨_, hsub⟩
  have hne : ∀ q : Q L M, rep q ∉ L.lattice → ℘[L] z ≠ ℘[L] (rep q) := by
    intro q hq heq
    exact hxB ⟨q, by simp only [hxq]; rw [← heq, hxz.1]⟩
  have haz : a * z ∉ L'.lattice := by
    intro h'
    apply hzM
    rw [hM, mem_scale_lattice_iff]
    refine ⟨a * z, h', ?_⟩
    simp [hau, ha0]

  have hXq : ∀ q : Q L M, ℘[L] (z + rep q) = fXq q x y := by
    intro q
    by_cases hq : rep q ∈ L.lattice
    · simp only [hfXq, if_pos hq]
      rw [← hxz.1]
      exact L.weierstrassP_add_coe z ⟨_, hq⟩
    · simp only [hfXq, if_neg hq, hxq, hyq]
      rw [(weierstrassP_add_eq L hzL hq (hne q hq)).1, addX_eq_chordX L (hne q hq), hxz.1, hxz.2]
  have hYq : ∀ q : Q L M, ℘'[L] (z + rep q) / 2 = fYq q x y := by
    intro q
    by_cases hq : rep q ∈ L.lattice
    · simp only [hfYq, if_pos hq]
      rw [← hxz.2, L.derivWeierstrassP_add_coe z ⟨_, hq⟩]
    · simp only [hfYq, if_neg hq, hxq, hyq]
      rw [(weierstrassP_add_eq L hzL hq (hne q hq)).2, addY_eq_chordY L (hne q hq), hxz.1, hxz.2]

  have hβ : mulHom L L' hL hL' a ha (.some x y h) = T L' hL' (a * z) := by
    rw [← hz]; exact mulHom_apply_T L L' hL hL' a ha z
  rw [T_apply, L'.toPoint_of_notMem hL' haz] at hβ
  refine exists_some_of_eq hβ ?_ ?_
  · rw [show a * z = (au : ℂ) * z from rfl, weierstrassP_mul_eq L' au z, hK z]
    simp only [hFX, hau, Units.val_mk0]
    congr 1
    rw [Finset.sum_congr rfl fun q _ => hXq q]
  · rw [show a * z = (au : ℂ) * z from rfl, derivWeierstrassP_mul_eq L' au z,
      deriv_coset_identity (L := L) (M := M) hLM hK hzM]
    simp only [hFY, hau, Units.val_mk0]
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun q _ => hYq q

end Main

end PeriodPair.MulToRat
p2m_reactivate "P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.PeriodPair P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.PeriodPair.MulToRat"
p2m_reactivate "P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.PeriodPair"

open PeriodPair.MulToRat in
theorem solution (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) : ∃ β ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve, ∀ z : ℂ, β (L.toPoint hL z) = L'.toPoint hL' (a * z) :=
  exists_mem_rationalHomSet L L' hL hL' a ha

end S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul
end P2MW
export P2MW.S_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul (solution)
