-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/00da1a32-076c-5e06-96d7-2441a2a4fb1a

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace Q1Classify13

variable {a b : ℚ}

noncomputable def ιC (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (x : ℍ[ℚ, a, b]) : Matrix (Fin 2) (Fin 2) ℂ :=
  (ι x).map (algebraMap ℝ ℂ)

theorem ιC_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (x y : ℍ[ℚ, a, b]) :
    ιC ι (x * y) = ιC ι x * ιC ι y := by
  simp only [ιC, map_mul, Matrix.map_mul]

theorem ιC_one (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) : ιC ι 1 = 1 := by
  simp only [ιC, map_one, Matrix.map_one (algebraMap ℝ ℂ) (map_zero _) (map_one _)]

theorem ιC_add (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (x y : ℍ[ℚ, a, b]) :
    ιC ι (x + y) = ιC ι x + ιC ι y := by
  ext i j; simp [ιC]

theorem ιC_smul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (r : ℚ) (x : ℍ[ℚ, a, b]) :
    ιC ι (r • x) = (r : ℂ) • ιC ι x := by
  ext i j
  simp only [ιC, map_smul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Rat.smul_def, map_mul]
  simp

noncomputable def orb (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℂ) : ℍ[ℚ, a, b] →ₗ[ℚ] (Fin 2 → ℂ) where
  toFun x := (ιC ι x).mulVec v
  map_add' x y := by rw [ιC_add, Matrix.add_mulVec]
  map_smul' r x := by
    rw [ιC_smul, Matrix.smul_mulVec, RingHom.id_apply, Rat.cast_smul_eq_qsmul]

end Q1Classify13

namespace Q1Classify13

variable {a b : ℚ}

theorem orb_apply (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℂ) (x : ℍ[ℚ, a, b]) :
    orb ι v x = (ιC ι x).mulVec v := rfl

theorem orb_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℂ) (x y : ℍ[ℚ, a, b]) :
    orb ι v (x * y) = (ιC ι x).mulVec (orb ι v y) := by
  rw [orb_apply, orb_apply, ιC_mul, Matrix.mulVec_mulVec]

theorem orb_injective (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    Function.Injective (orb ι v) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  by_contra hne
  obtain ⟨u, rfl⟩ := hdiv x hne
  apply hv
  calc v = orb ι v 1 := by rw [orb_apply, ιC_one, Matrix.one_mulVec]
    _ = orb ι v (↑u⁻¹ * ↑u) := by rw [Units.inv_mul]
    _ = (ιC ι ↑u⁻¹).mulVec (orb ι v ↑u) := orb_mul ι v _ _
    _ = 0 := by rw [hx, Matrix.mulVec_zero]

theorem exists_orb_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (L : Submodule ℤ (Fin 2 → ℂ)) (e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ)) (hL : L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, (ιC ι x).mulVec v ∈ L) {v : Fin 2 → ℂ} (hvL : v ∈ L) (hv : v ≠ 0) :
    ∀ w ∈ L, ∃ x : ℍ[ℚ, a, b], orb ι v x = w := by
  let V : Submodule ℚ (Fin 2 → ℂ) := Submodule.span ℚ (L : Set (Fin 2 → ℂ))
  have hV : V = Submodule.span ℚ (Set.range e) := by
    show Submodule.span ℚ (L : Set (Fin 2 → ℂ)) = _
    rw [hL]
    exact Submodule.span_span_of_tower ℤ ℚ (Set.range e)
  haveI : Module.Finite ℚ V := by
    rw [hV]; exact FiniteDimensional.span_of_finite ℚ (Set.finite_range e)
  have hVle : Module.finrank ℚ V ≤ 4 := by
    rw [hV]
    exact (finrank_range_le_card (R := ℚ) e).trans (by simp)
  have hR : LinearMap.range (orb ι v) ≤ V := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := by rw [hΛ.spanTop]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hstab y hy v hvL)
    | zero => rw [map_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact V.add_mem hy hz
    | smul r y _ hy => rw [map_smul]; exact V.smul_mem r hy
  have hR4 : Module.finrank ℚ (LinearMap.range (orb ι v)) = 4 := by
    rw [LinearMap.finrank_range_of_inj (orb_injective ι hdiv hv), QuaternionAlgebra.finrank_eq_four]
  have hEq : LinearMap.range (orb ι v) = V :=
    Submodule.eq_of_le_of_finrank_le hR (by rw [hR4]; exact hVle)
  intro w hw
  have : w ∈ V := Submodule.subset_span hw
  rw [← hEq] at this
  exact this

theorem false_of_full_of_smul_real (e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ)) (L : Submodule ℤ (Fin 2 → ℂ))
    (hL : L = Submodule.span ℤ (Set.range e)) (lam : ℂ)
    (h : ∀ u ∈ L, ∃ s : Fin 2 → ℝ, u = lam • fun i => ((s i : ℝ) : ℂ)) : False := by
  classical
  let bv : Fin 2 → (Fin 2 → ℂ) := fun j => lam • fun i => ((Pi.single j (1 : ℝ) : Fin 2 → ℝ) i : ℂ)
  let T : Submodule ℝ (Fin 2 → ℂ) := Submodule.span ℝ (Set.range bv)
  have hT2 : Module.finrank ℝ T ≤ 2 := (finrank_range_le_card (R := ℝ) bv).trans (by simp)
  have hmem : ∀ s : Fin 2 → ℝ, (lam • fun i => ((s i : ℝ) : ℂ)) ∈ T := by
    intro s
    have : (lam • fun i => ((s i : ℝ) : ℂ)) = ∑ j : Fin 2, s j • bv j := by
      ext i
      simp only [bv, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Fin.sum_univ_two, Pi.single_apply]
      fin_cases i <;> simp <;> ring
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hLT : ∀ u ∈ L, u ∈ T := by
    intro u hu; obtain ⟨s, rfl⟩ := h u hu; exact hmem s
  have htop : (⊤ : Submodule ℝ (Fin 2 → ℂ)) ≤ T := by
    rw [← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hLT _ (by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩)
  have h4 : 4 ≤ Module.finrank ℝ T := by
    have := Submodule.finrank_mono htop
    rw [finrank_top, Module.finrank_eq_card_basis e] at this
    simpa using this
  omega

theorem mulVec_real (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (y : ℍ[ℚ, a, b]) (s : Fin 2 → ℝ) :
    (ιC ι y).mulVec (fun i => ((s i : ℝ) : ℂ)) = fun i => ((((ι y).mulVec s) i : ℝ) : ℂ) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℝ ℂ) (ι y) s i).symm

theorem core {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L)
    (principal : ∀ I : Submodule ℤ ℍ[ℚ, a, b], I.FG → Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤ →
      (∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I) →
      ∃ x₀ : ℍ[ℚ, a, b], x₀ ≠ 0 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ I ↔ ∃ z ∈ Λ, z * x₀ = y) :
    ∃ (τ : ℂ) (c : ℂ), τ.im ≠ 0 ∧ c ≠ 0 ∧
      ∀ w : Fin 2 → ℂ, w ∈ c • L ↔ ∃ x ∈ Λ, ((ι x).map (algebraMap ℝ ℂ)).mulVec ![τ, 1] = w := by
  classical
  obtain ⟨e, hL⟩ := hfull
  have hstab' : ∀ x ∈ Λ, ∀ v ∈ L, (ιC ι x).mulVec v ∈ L := hstab

  have hv : (e 0 : Fin 2 → ℂ) ≠ 0 := e.ne_zero 0
  have hvL : (e 0 : Fin 2 → ℂ) ∈ L := by rw [hL]; exact Submodule.subset_span ⟨0, rfl⟩
  set v : Fin 2 → ℂ := e 0 with hvdef

  let I : Submodule ℤ ℍ[ℚ, a, b] := L.comap ((orb ι v).restrictScalars ℤ)
  have hImem : ∀ z, z ∈ I ↔ orb ι v z ∈ L := fun z => Iff.rfl
  have hI1 : (1 : ℍ[ℚ, a, b]) ∈ I := by rw [hImem, orb_apply, ιC_one, Matrix.one_mulVec]; exact hvL
  have hIstab : ∀ x ∈ Λ, ∀ y ∈ I, x * y ∈ I := by
    intro x hx y hy; rw [hImem, orb_mul]; exact hstab' x hx _ ((hImem y).1 hy)
  have hImap : I.map ((orb ι v).restrictScalars ℤ) = L := by
    apply le_antisymm (Submodule.map_comap_le _ _)
    intro w hw
    obtain ⟨x, hx⟩ := exists_orb_eq hΛ ι hdiv L e hL hstab' hvL hv w hw
    exact ⟨x, by show orb ι v x ∈ L; rw [hx]; exact hw, hx⟩
  have hIfg : I.FG := by
    apply Submodule.fg_of_fg_map_injective ((orb ι v).restrictScalars ℤ)
      (by simpa using orb_injective ι hdiv hv)
    rw [hImap, hL]
    exact Submodule.fg_span (Set.finite_range e)
  have hIspan : Submodule.span ℚ (I : Set ℍ[ℚ, a, b]) = ⊤ := by
    apply top_le_iff.mp
    rw [← hΛ.spanTop]
    apply Submodule.span_mono
    intro x hx
    have := hIstab x hx 1 hI1
    rwa [mul_one] at this
  obtain ⟨x₀, -, hx₀⟩ := principal I hIfg hIspan hIstab

  set w : Fin 2 → ℂ := orb ι v x₀ with hwdef
  have hLw : ∀ u, u ∈ L ↔ ∃ y ∈ Λ, (ιC ι y).mulVec w = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨z, hz⟩ := exists_orb_eq hΛ ι hdiv L e hL hstab' hvL hv u hu
      have hzI : z ∈ I := by rw [hImem, hz]; exact hu
      obtain ⟨y, hy, rfl⟩ := (hx₀ z).1 hzI
      exact ⟨y, hy, by rw [← orb_mul]; exact hz⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← orb_mul, ← hImem]
      exact (hx₀ _).2 ⟨y, hy, rfl⟩

  have hw1 : w 1 ≠ 0 := by
    intro h0
    apply false_of_full_of_smul_real e L hL (w 0)
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hLw u).1 hu
    refine ⟨(ι y).mulVec ![1, 0], ?_⟩
    have : w = (w 0) • fun i => ((![(1 : ℝ), 0] i : ℝ) : ℂ) := by
      ext i; fin_cases i <;> simp [h0]
    conv_lhs => rw [this, Matrix.mulVec_smul, mulVec_real]
  have him : (w 0 / w 1).im ≠ 0 := by
    intro h0
    apply false_of_full_of_smul_real e L hL (w 1)
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hLw u).1 hu
    refine ⟨(ι y).mulVec ![(w 0 / w 1).re, 1], ?_⟩
    have hre : ((w 0 / w 1).re : ℂ) = w 0 / w 1 := by
      apply Complex.ext <;> simp [h0]
    have : w = (w 1) • fun i => ((![(w 0 / w 1).re, (1 : ℝ)] i : ℝ) : ℂ) := by
      ext i; fin_cases i
      · simp [hre, mul_div_cancel₀ _ hw1]
      · simp
    conv_lhs => rw [this, Matrix.mulVec_smul, mulVec_real]

  refine ⟨w 0 / w 1, (w 1)⁻¹, him, inv_ne_zero hw1, fun u => ?_⟩
  have hcw : (w 1)⁻¹ • w = ![w 0 / w 1, 1] := by
    ext i; fin_cases i
    · simp [div_eq_inv_mul]
    · simp [inv_mul_cancel₀ hw1]
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (hLw s).1 hs
    exact ⟨y, hy, by rw [← hcw, Matrix.mulVec_smul]; rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(ιC ι y).mulVec w, (hLw _).2 ⟨y, hy, rfl⟩, ?_⟩
    rw [← Matrix.mulVec_smul, hcw]
    rfl

end Q1Classify13

open Q1Classify13 in

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L) :
    ∃ (τ : ℂ) (c : ℂ), τ.im ≠ 0 ∧ c ≠ 0 ∧
      ∀ w : Fin 2 → ℂ, w ∈ c • L ↔ ∃ x ∈ Λ, ((ι x).map (algebraMap ℝ ℂ)).mulVec ![τ, 1] = w :=
  core hΛ.isOrder (fun x hx => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx) ι L hfull hstab
    (fun I hIfg hIspan hIstab =>
      QuaternionAlgebra.IsMaximalOrder.exists_eq_map_mulRight_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ I hIfg hIspan hIstab)

end S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem (solution)
