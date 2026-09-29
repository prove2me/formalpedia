-- Prove2me | solution 1 for PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8c2f404b-5f57-577a-b424-c363381ad8bf

import Mathlib
import Theorems.Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
import Theorems.Thm_WLight_weierstrassP_qExpansion_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex Filter Function ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology Manifold Matrix Real

namespace WPGamma1

theorem indep (τ : ℍ) : LinearIndependent ℝ ![(τ : ℂ), 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero, add_zero,
    Complex.zero_im, Complex.add_re, Complex.smul_re, Complex.one_re, mul_one, Complex.zero_re] at him hre
  have hs : s = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h τ.im_ne_zero
  subst hs
  simp only [zero_mul, zero_add] at hre
  exact ⟨rfl, hre⟩

def L (τ : ℍ) : PeriodPair := ⟨τ, 1, indep τ⟩

theorem hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1 := fun _ => ⟨rfl, rfl⟩

theorem weierstrassP_eq_of_hL (L' : ℍ → PeriodPair)
    (hL' : ∀ τ : ℍ, (L' τ).ω₁ = (τ : ℂ) ∧ (L' τ).ω₂ = 1) (τ : ℍ) :
    (L' τ).weierstrassP = (L τ).weierstrassP := by
  have h : (L' τ).lattice = (L τ).lattice := by
    rw [PeriodPair.lattice, PeriodPair.lattice, (hL' τ).1, (hL' τ).2, (hL τ).1, (hL τ).2]
  funext z
  simp only [PeriodPair.weierstrassP]
  rw [h]

variable (M : ℕ) [NeZero M]

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def Wraw (b : Fin 2 → ZMod M) (τ : ℍ) : ℂ :=
  (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / M)

def cst : ℂ := 12 * ((2 * π * I) ^ 2)⁻¹

def Wfun (t : ZMod M) (τ : ℍ) : ℂ := cst * (L τ).weierstrassP ((t.val : ℂ) / M)

theorem Wfun_eq (t : ZMod M) : Wfun M t = cst • Wraw M ![0, t] := by
  funext τ
  simp [Wfun, Wraw, Pi.smul_apply, smul_eq_mul]

abbrev redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  ((γ : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M))

theorem redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN M γ i j = ((γ i j : ℤ) : ZMod M) := rfl

theorem K1 (t : ZMod M) :
    (∃ F : ModularForm Γ(M) 2, ⇑F = Wraw M ![0, t]) ∧
    (∀ γ : SL(2, ℤ), Wraw M ![0, t] ∣[(2 : ℤ)] γ = Wraw M (![0, t] ᵥ* redN M γ)) := by
  obtain ⟨h1, h2, -⟩ :=
    PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty L hL M ![0, t]
  exact ⟨h1, h2⟩

theorem vecMul_redN (t : ZMod M) (γ : SL(2, ℤ)) :
    (![0, t] ᵥ* redN M γ : Fin 2 → ZMod M) =
      ![t * ((γ 1 0 : ℤ) : ZMod M), t * ((γ 1 1 : ℤ) : ZMod M)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem Wfun_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    Wfun M t ∣[(2 : ℤ)] γ = Wfun M (t * ((γ 1 1 : ℤ) : ZMod M)) := by
  have h10 : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  rw [Wfun_eq, Wfun_eq, ModularForm.SL_smul_slash, (K1 M t).2 γ, vecMul_redN, h10, mul_zero]

theorem Wfun_slash_of_mem_Gamma1 (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 M) :
    Wfun M t ∣[(2 : ℤ)] γ = Wfun M t := by
  have h := (Gamma1_mem M γ).mp hγ
  rw [Wfun_slash M t γ (Gamma1_in_Gamma0 M hγ), h.2.1, mul_one]

def FΓ (t : ZMod M) : ModularForm Γ(M) 2 := cst • (K1 M t).1.choose

theorem coe_FΓ (t : ZMod M) : (⇑(FΓ M t) : ℍ → ℂ) = Wfun M t := by
  rw [FΓ, IsGLPos.coe_smul, (K1 M t).1.choose_spec, Wfun_eq]

def Wform (t : ZMod M) : ModularForm Γ₁ᴳ 2 where
  toFun := Wfun M t
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := Wfun_slash_of_mem_Gamma1 M t γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := by
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Wfun M t)
    rw [← coe_FΓ M t]
    exact (FΓ M t).holo'
  bdd_at_cusps' {cu} hcu := by
    have hcu' : IsCusp cu Γ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu ⊢
      exact hcu
    change cu.IsBoundedAt (Wfun M t) (2 : ℤ)
    rw [← coe_FΓ M t]
    exact (FΓ M t).bdd_at_cusps' hcu'

theorem coe_Wform (t : ZMod M) : (⇑(Wform M t) : ℍ → ℂ) = Wfun M t := rfl

theorem Wform_apply (t : ZMod M) (τ : ℍ) :
    Wform M t τ = 12 * ((2 * π * I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M) := rfl

section QExp

def ζ : ℂ := cexp (2 * π * I / M)

def chi (t : ZMod M) (d : ℕ) : ℂ := ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d) - 2

theorem norm_ζ : ‖ζ M‖ = 1 := by
  rw [ζ, show (2 * π * I / M : ℂ) = ((2 * π / M : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_chi_le (t : ZMod M) (d : ℕ) : ‖chi M t d‖ ≤ 4 := by
  rw [chi]
  calc ‖ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d) - 2‖
        ≤ ‖ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖ζ M ^ (t.val * d)‖ + ‖(ζ M)⁻¹ ^ (t.val * d)‖) + ‖(2 : ℂ)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = 4 := by
        rw [norm_pow, norm_pow, norm_inv, norm_ζ, inv_one, one_pow, Complex.norm_two]; norm_num

def acoef (t : ZMod M) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) * chi M t d

def wc (t : ZMod M) (n : ℕ) : ℂ :=
  if n = 0 then 1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2
  else 12 * ((∑ d ∈ n.divisors, (d : ℂ) * (ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d))) -
    2 * ∑ d ∈ n.divisors, (d : ℂ))

theorem wc_of_ne_zero (t : ZMod M) {n : ℕ} (hn : n ≠ 0) : wc M t n = 12 * acoef M t n := by
  rw [wc, if_neg hn, acoef]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [chi]; ring

def qq (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ))

theorem norm_qq_lt_one (τ : ℍ) : ‖qq τ‖ < 1 := norm_exp_two_pi_I_lt_one τ

theorem qParam_one (τ : ℍ) : Periodic.qParam 1 (τ : ℂ) = qq τ := by
  simp [Periodic.qParam, qq]

theorem qM_pow (τ : ℍ) : cexp (2 * π * I * (τ : ℂ) / M) ^ M = qq τ := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [qq, ← Complex.exp_nat_mul]
  congr 1
  field_simp

def term (t : ZMod M) (τ : ℍ) (p : ℕ+ × ℕ+) : ℂ :=
  ((p.2 : ℕ) : ℂ) * chi M t (p.2 : ℕ) * qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))

theorem summable_term (t : ZMod M) (τ : ℍ) : Summable (term M t τ) := by
  have hs : Summable fun c : ℕ+ × ℕ+ => ((c.2 : ℕ) : ℂ) ^ 1 * qq τ ^ ((c.1 : ℕ) * (c.2 : ℕ)) :=
    summable_prod_mul_pow 1 (norm_qq_lt_one τ)
  refine Summable.of_norm_bounded (g := fun c : ℕ+ × ℕ+ =>
    4 * ‖((c.2 : ℕ) : ℂ) ^ 1 * qq τ ^ ((c.1 : ℕ) * (c.2 : ℕ))‖) (hs.norm.mul_left 4) fun p => ?_
  simp only [pow_one]
  rw [term, norm_mul, norm_mul, norm_mul]
  calc ‖((p.2 : ℕ) : ℂ)‖ * ‖chi M t (p.2 : ℕ)‖ * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖
        ≤ ‖((p.2 : ℕ) : ℂ)‖ * 4 * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖ := by
          gcongr
          exact norm_chi_le M t _
    _ = 4 * (‖((p.2 : ℕ) : ℂ)‖ * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖) := by ring

theorem Wfun_eq_tsum (t : ZMod M) (ht : t ≠ 0) (τ : ℍ) :
    Wfun M t τ = (1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2) + 12 * ∑' p : ℕ+ × ℕ+, term M t τ p := by
  obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
  have htv : t.val ≠ 0 := fun h => ht ((ZMod.val_eq_zero t).mp h)
  obtain ⟨hexp, -⟩ := h23 L hL M 0 t.val (NeZero.pos M) (ZMod.val_lt t) (Or.inr htv)
  have h := hexp τ
  simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, mul_one, add_zero, Nat.sub_zero] at h
  have hI : (2 * π * I : ℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  have hterm : (fun p : ℕ+ × ℕ+ => ((p.2 : ℕ) : ℂ) *
      (cexp (2 * π * I / M) ^ (t.val * (p.2 : ℕ)) * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) +
        (cexp (2 * π * I / M))⁻¹ ^ (t.val * (p.2 : ℕ)) * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) -
        2 * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)))) = term M t τ := by
    funext p
    have hq : cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) = qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
      rw [show (p.1 : ℕ) * M * (p.2 : ℕ) = M * ((p.1 : ℕ) * (p.2 : ℕ)) by ring, pow_mul, qM_pow]
    rw [hq, term, chi, ζ]
    ring
  rw [Wfun, h, hterm, cst, ζ]
  field_simp
  ring

theorem hasSum_acoef (t : ZMod M) (τ : ℍ) :
    HasSum (fun n : ℕ+ => acoef M t n * qq τ ^ (n : ℕ)) (∑' p : ℕ+ × ℕ+, term M t τ p) := by
  have h0 : HasSum (term M t τ) (∑' p : ℕ+ × ℕ+, term M t τ p) := (summable_term M t τ).hasSum
  have h1 : HasSum (term M t τ ∘ sigmaAntidiagonalEquivProd) (∑' p : ℕ+ × ℕ+, term M t τ p) :=
    (Equiv.hasSum_iff sigmaAntidiagonalEquivProd).mpr h0
  refine h1.sigma fun n => ?_

  have hfin : ∑ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
      (term M t τ ∘ sigmaAntidiagonalEquivProd) ⟨n, c⟩ = acoef M t n * qq τ ^ (n : ℕ) := by
    have e1 : ∀ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
        (term M t τ ∘ sigmaAntidiagonalEquivProd) ⟨n, c⟩ =
          ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2) := by
      intro c
      rfl
    simp_rw [e1]
    rw [show (∑ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
        ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2)) =
        ∑ c ∈ ((n : ℕ).divisorsAntidiagonal).attach,
          ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2) from rfl]
    rw [Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun c : ℕ × ℕ => ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (c.1 * c.2))]
    have e2 : ∀ c ∈ (n : ℕ).divisorsAntidiagonal,
        ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (c.1 * c.2) = ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (n : ℕ) := by
      intro c hc
      rw [(Nat.mem_divisorsAntidiagonal.mp hc).1]
    rw [Finset.sum_congr rfl e2, Nat.sum_divisorsAntidiagonal' (fun _ j => ((j : ℕ) : ℂ) * chi M t j * qq τ ^ (n : ℕ)),
      acoef, Finset.sum_mul]
  rw [← hfin]
  exact hasSum_fintype _

theorem hasSum_wc (t : ZMod M) (ht : t ≠ 0) (τ : ℍ) :
    HasSum (fun n : ℕ => wc M t n • Periodic.qParam 1 (τ : ℂ) ^ n) (Wform M t τ) := by
  rw [coe_Wform, Wfun_eq_tsum M t ht τ]
  set A : ℂ := 1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2 with hA
  set T : ℂ := ∑' p : ℕ+ × ℕ+, term M t τ p with hT

  set G : ℕ → ℂ := fun n => if n = 0 then 0 else 12 * (acoef M t n * qq τ ^ n) with hG
  have hG1 : HasSum G (12 * T) := by
    have h := (hasSum_acoef M t τ).mul_left 12
    have hzero : ∀ x ∉ Set.range (PNat.val), G x = 0 := by
      intro x hx
      have : x = 0 := by
        by_contra hx0
        exact hx ⟨⟨x, Nat.pos_of_ne_zero hx0⟩, rfl⟩
      rw [hG, this]; simp
    rw [← PNat.coe_injective.hasSum_iff hzero]
    refine h.congr_fun fun n => ?_
    simp [hG, n.ne_zero]
  have hG0 : HasSum (fun n : ℕ => if n = 0 then A else 0) A := hasSum_ite_eq 0 A
  have hsum := hG0.add hG1
  refine hsum.congr_fun fun n => ?_
  rw [qParam_one]
  by_cases hn : n = 0
  · subst hn
    simp [hG, wc, hA]
  · simp only [hG, if_neg hn, wc_of_ne_zero M t hn, zero_add, smul_eq_mul]
    ring

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ₁ᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem qExpansion_Wform_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (Wform M t)).coeff n = wc M t n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods M)
    (f := Wform M t) (hasSum_wc M t ht) n).symm

end QExp

theorem main :
    ∃ W : ZMod M → ModularForm Γ₁ᴳ 2,
      (∀ (L' : ℍ → PeriodPair), (∀ τ : ℍ, (L' τ).ω₁ = (τ : ℂ) ∧ (L' τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : ℍ),
          W t τ = 12 * ((2 * π * I) ^ 2)⁻¹ * (L' τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
        (⇑(W t) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * cexp (2 * π * I / M) ^ t.val / (1 - cexp (2 * π * I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (cexp (2 * π * I / M) ^ (t.val * d) + (cexp (2 * π * I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) := by
  refine ⟨Wform M, fun L' hL' t τ => ?_, fun t γ hγ => Wfun_slash M t γ hγ,
    fun t ht n => qExpansion_Wform_coeff M t ht n⟩
  rw [Wform_apply, weierstrassP_eq_of_hL L' hL' τ]

end WPGamma1

end

open scoped MatrixGroups ModularForm Real in

theorem solution (M : ℕ) [NeZero M] :
    ∃ W : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ (L : UpperHalfPlane → PeriodPair),
        (∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : UpperHalfPlane),
          W t τ = 12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(W t) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) :=
  WPGamma1.main M

end S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
end P2MW
export P2MW.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff (solution)
