-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.indSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:02.835434+00:00
-- url     : https://prove2.me/submissions/b7704e00-6a46-40a9-91b8-8a2342734559

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_FiniteOfIntegralBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_IndSetFinite
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_exists_smul_mem
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_finite_of_integral_bound
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_herm_swap
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_add_left
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_cs
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_pos
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_mj_smul_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions NumberField
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
    (hzz : ∀ τ : E →+* ℂ, (τ (S.hT z z)).re < 0)
    (hpos : ∀ τ : E →+* ℂ, ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT x y)) (hzΛ : z ∈ Λ) :
    (indSet X P z Λ).Finite := by
  classical
  set Xc := X.comap P.subtype
  have hzz0 : S.hT z z ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h; have := hzz τ; rw [h, map_zero] at this; simp at this

  set bB := Module.finBasis E P
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • (bB i : S.V) ∈ Λ := fun i => exists_smul_mem Λ hΛ _
  choose d hd0 hdΛ using hd
  have hd0' : ∀ i, algebraMap (𝓞 E) E (d i) ≠ 0 := fun i => by
    rw [ne_eq, ← map_zero (algebraMap (𝓞 E) E), (IsFractionRing.injective (𝓞 E) E).eq_iff]
    exact hd0 i
  set b := bB.unitsSMul (fun i => Units.mk0 _ (hd0' i))
  have hbΛ : ∀ i, ((b i : P) : S.V) ∈ Λ := by
    intro i
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0,
      algebraMap_smul]
    exact hdΛ i

  set cf : Fin (Module.finrank E P) → ℝ := fun i =>
    ∑ τ : E →+* ℂ, |(τ (mj S z (b i : S.V) (b i : S.V))).re| with hcf
  set C : ℝ := ∑ i, cf i with hCdef
  have hC : ∀ i (τ : E →+* ℂ), (τ (mj S z (b i : S.V) (b i : S.V))).re ≤ C := by
    intro i τ
    have h1 : |(τ (mj S z (b i : S.V) (b i : S.V))).re| ≤ cf i :=
      Finset.single_le_sum (f := fun (τ : E →+* ℂ) => |(τ (mj S z (b i : S.V) (b i : S.V))).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have h2 : cf i ≤ C := Finset.single_le_sum (f := cf)
      (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans (h1.trans h2)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

  set Y : Set (P ⧸ Xc) := {q | ∃ y : P, (y : S.V) ∈ Λ ∧
    (∀ τ : E →+* ℂ, (τ (mj S z y y)).re ≤ C) ∧ q = Submodule.Quotient.mk y}

  let mjR : Fin (Module.finrank E P) → S.V →ₗ[E] E := fun j =>
    S.hT (b j : S.V) - (2 / S.hT z z * S.hT (b j : S.V) z) • S.hT z
  have hmjR : ∀ j y, mjR j y = mj S z (b j : S.V) y := by
    intro j y; simp only [mjR, mj, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
  let Pm : P →ₗ[E] (Fin (Module.finrank E P) → E) := LinearMap.pi fun j => (mjR j).comp P.subtype
  have hPm : ∀ (y : P) j, Pm y j = mj S z (b j : S.V) y := by
    intro y j; simp [Pm, hmjR]
  have hker : Xc ≤ LinearMap.ker Pm := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext j
    rw [hPm]
    have h1 : S.hT (b j : S.V) y = 0 := by
      rw [herm_swap, hPX (y : S.V) hy _ (b j).2, star_zero]
    have h2 : S.hT z y = 0 := by rw [herm_swap, hPX (y : S.V) hy _ hzP, star_zero]
    simp [mj, h1, h2]
  let g : (P ⧸ Xc) →ₗ[E] (Fin (Module.finrank E P) → E) := Xc.liftQ Pm hker
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq
    have hw : ∀ j, mj S z (b j : S.V) w = 0 := fun j => by rw [← hPm, hq]; rfl
    have hall : ∀ v : P, mj S z v w = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range b) := by rw [b.span_eq]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hw j
      | zero => simpa using mj_smul_left (S := S) z 0 (0 : S.V) w
      | add x y _ _ h1 h2 => rw [Submodule.coe_add, mj_add_left, h1, h2, add_zero]
      | smul c x _ h => rw [Submodule.coe_smul, mj_smul_left, h, mul_zero]
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hw0 := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) w w.2).2 (by rw [hall w]; simp)
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hw0
  have hYfin : Y.Finite := by
    apply Set.Finite.of_finite_image (f := g) _ hg.injOn
    apply (Set.Finite.pi (t := fun _ => {a : E | IsIntegral ℤ (S.hT z z * a) ∧
      ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}) fun _ => finite_of_integral_bound _ hzz0 C).subset
    rintro _ ⟨q, ⟨y, hyΛ, hyC, rfl⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    have hgj : g (Submodule.Quotient.mk y) j = mj S z (b j : S.V) y := by
      simp only [g, Submodule.liftQ_apply]; exact hPm y j
    rw [hgj]
    constructor
    · have e1 : S.hT z z * mj S z (b j : S.V) y =
          S.hT z z * S.hT (b j : S.V) y - (S.hT (b j : S.V) z * S.hT z y + S.hT (b j : S.V) z * S.hT z y) := by
        simp only [mj]; field_simp; ring
      rw [e1]
      refine IsIntegral.sub (IsIntegral.mul (hint _ hzΛ _ hzΛ) (hint _ (hbΛ j) _ hyΛ))
        (IsIntegral.add (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ))
          (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)))
    · intro τ
      have hcs := mj_cs hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ _ (b j).2 y.2
      have ha := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ (b j).2).1
      have hb := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ y.2).1
      have h1 := hC j τ
      have h2 := hyC τ
      have hsq : ‖τ (mj S z (b j : S.V) y)‖ ^ 2 ≤ C ^ 2 := by
        rw [Complex.sq_norm]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp hsq

  apply Set.Finite.of_finite_image (f := fun φ i => φ (Submodule.Quotient.mk (b i)))
  · apply (Set.Finite.pi (t := fun _ => Y) fun _ => hYfin).subset
    rintro _ ⟨φ, ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨⟨γ (b i : S.V), hγP _ (b i).2⟩, hγΛ _ (hbΛ i), fun τ => ?_, hφ _ _⟩
    have e1 : ∀ x : S.V, S.hT (γ x) z = S.hT x z := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso x z
    have e2 : ∀ x : S.V, S.hT z (γ x) = S.hT z x := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso z x
    have : mj S z (γ (b i : S.V)) (γ (b i : S.V)) = mj S z (b i : S.V) (b i : S.V) := by
      simp only [mj, hiso, e1, e2]
    simp only [this]
    exact hC i τ
  · rintro φ ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩ φ' ⟨γ', hiso', hγz', hγΛ', hγP', hφ'⟩ heq
    let ψ : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ : S.V →ₗ[E] S.V).restrict hγP
    let ψ' : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ' : S.V →ₗ[E] S.V).restrict hγP'
    have hψ : ∀ x : P, φ (Submodule.Quotient.mk x) = ψ x := fun x => by
      rw [hφ x (hγP _ x.2)]; rfl
    have hψ' : ∀ x : P, φ' (Submodule.Quotient.mk x) = ψ' x := fun x => by
      rw [hφ' x (hγP' _ x.2)]; rfl
    have hψψ : ψ = ψ' := b.ext fun i => by
      rw [← hψ, ← hψ']; exact congrFun heq i
    funext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψ, hψ', hψψ]
end PI.AutLzFinite.SlopeTestRemainingChoices
