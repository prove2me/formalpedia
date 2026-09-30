-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T16:58:38.090782+00:00
-- url     : https://prove2.me/submissions/0156d666-38ff-4f4b-9681-5f052a8cd48a

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set TranscendenceTheory MvPolynomial
open scoped Topology
open WeierstrassEllipticZeta

private lemma extension_forms_homogeneous (g₂ g₃ : ℂ) :
    extensionQuadric.IsHomogeneous 2 ∧ (extensionCubic g₂ g₃).IsHomogeneous 3 := by
  constructor
  · exact ((isHomogeneous_X ℂ 0).mul (isHomogeneous_X ℂ 4)).sub
      ((isHomogeneous_X ℂ 2).mul (isHomogeneous_X ℂ 3)) |>.sub
        (isHomogeneous_C_mul_X_pow 2 1 2)
  · exact (((isHomogeneous_X ℂ 0).mul (isHomogeneous_X_pow 2 2)).sub
      (isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((isHomogeneous_C_mul_X_pow g₂ 0 2).mul (isHomogeneous_X ℂ 1)) |>.add
          (isHomogeneous_C_mul_X_pow g₃ 0 3)

private lemma extension_forms_smul (g₂ g₃ c : ℂ) (v : Fin 5 → ℂ) :
    MvPolynomial.eval (c • v) extensionQuadric =
        c ^ 2 * MvPolynomial.eval v extensionQuadric ∧
      MvPolynomial.eval (c • v) (extensionCubic g₂ g₃) =
        c ^ 3 * MvPolynomial.eval v (extensionCubic g₂ g₃) := by
  simp [extensionQuadric, extensionCubic, Pi.smul_apply, smul_eq_mul]
  constructor <;> ring

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ))
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) :
    extensionQuadric.IsHomogeneous 2 ∧ (extensionCubic L.g₂ L.g₃).IsHomogeneous 3 ∧
      (∀ (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0),
        Projectivization.mk ℂ v hv = P e →
          MvPolynomial.eval v extensionQuadric = 0 ∧
            MvPolynomial.eval v (extensionCubic L.g₂ L.g₃) = 0) ∧
      ∃ A : GraphQuotientExtension L.lattice η → ProjectiveExtensionLocus L.g₂ L.g₃,
        ∀ e, (A e).val = P e := by
  have hSa (Q : MvPolynomial (Fin 5) ℂ) :
      AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => S j z) Q) Set.univ := by
    intro z _
    exact AnalyticAt.aeval_mvPolynomial (fun j => hS j z (Set.mem_univ _)) Q
  have hquad : (fun z => MvPolynomial.eval (fun j => S j z) extensionQuadric) = 0 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hSa extensionQuadric) analyticOnNhd_const
      (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    change MvPolynomial.eval (fun j => S j z) extensionQuadric = (0 : ℂ)
    simp [extensionQuadric, hS_value z hz]
    ring
  have hcubic : (fun z => MvPolynomial.eval (fun j => S j z)
      (extensionCubic L.g₂ L.g₃)) = 0 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hSa (extensionCubic L.g₂ L.g₃))
      analyticOnNhd_const (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    change MvPolynomial.eval (fun j => S j z) (extensionCubic L.g₂ L.g₃) = (0 : ℂ)
    simp [extensionCubic, hS_value z hz]
    linear_combination D.sigma z ^ 9 * (L.derivWeierstrassP_sq z hz)
  have hV (z u : ℂ) :
      MvPolynomial.eval
        ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z]
        extensionQuadric = 0 ∧
      MvPolynomial.eval
        ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z]
        (extensionCubic L.g₂ L.g₃) = 0 := by
    have hq := congrFun hquad z
    have hc := congrFun hcubic z
    simp [extensionQuadric, extensionCubic] at hq hc ⊢
    constructor
    · linear_combination hq
    · exact hc
  have heq (e : GraphQuotientExtension L.lattice η) (v : Fin 5 → ℂ) (hv : v ≠ 0)
      (hp : Projectivization.mk ℂ v hv = P e) :
      MvPolynomial.eval v extensionQuadric = 0 ∧
        MvPolynomial.eval v (extensionCubic L.g₂ L.g₃) = 0 := by
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective e
    obtain ⟨hvu, hpu⟩ := hP z u
    rw [hpu] at hp
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
    rw [← hc]
    have hs := extension_forms_smul L.g₂ L.g₃ c
      ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z]
    simpa [(hV z u).1, (hV z u).2] using hs
  refine ⟨(extension_forms_homogeneous L.g₂ L.g₃).1,
    (extension_forms_homogeneous L.g₂ L.g₃).2, heq, ?_⟩
  exact ⟨fun e => ⟨P e, heq e (P e).rep (P e).rep_nonzero (P e).mk_rep⟩,
    fun _ => rfl⟩

