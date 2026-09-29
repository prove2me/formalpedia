-- Prove2me | solution 1 for PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/32f0422b-363e-56e3-921a-7280f755b5dc

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PadicAlgCl_exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional
import Theorems.Thm_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang
import Theorems.Thm_PadicAlgCl_mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one
import Theorems.Thm_PadicAlgCl_apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime
import Theorems.Thm_PadicAlgCl_exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self
import Theorems.Thm_PadicAlgCl_inertiaSubgroupIn_normal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open scoped TensorProduct
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace U3

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev Gal := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
abbrev GalO := PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p

theorem mem_fixingSubgroup_of_agree {σ : Gal p} {τ : GalO p K} (h : ∀ t, τ t = σ t) : σ ∈ K.fixingSubgroup := by
  have : PadicAlgCl.ringOfIntegers.restrictScalarsRat p K τ = σ := AlgEquiv.ext fun t => by
    rw [PadicAlgCl.ringOfIntegers.restrictScalarsRat_apply]; exact h t
  rw [← this]; exact PadicAlgCl.ringOfIntegers.restrictScalarsRat_mem_fixingSubgroup p K τ

theorem eq_galToAlgEquiv_of_agree {σ : Gal p} {τ : GalO p K} (h : ∀ t, τ t = σ t) :
    τ = PadicAlgCl.ringOfIntegers.galToAlgEquiv p K ⟨σ, mem_fixingSubgroup_of_agree p K h⟩ :=
  AlgEquiv.ext fun t => by rw [PadicAlgCl.ringOfIntegers.galToAlgEquiv_apply]; exact h t

theorem norm_det_sub_one_le {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (f : Module.End ℤ_[p] T) (k : ℕ) (hf : ∀ t : T, ∃ s : T, f t - t = ((p : ℤ_[p]) ^ k) • s) :
    ‖LinearMap.det f - 1‖ ≤ ‖(p : ℤ_[p])‖ ^ k := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] T
  haveI : Fintype (Module.Free.ChooseBasisIndex ℤ_[p] T) := inferInstance
  set I : Ideal ℤ_[p] := Ideal.span {((p : ℤ_[p]) ^ k)} with hI

  have hentry : ∀ i j, (LinearMap.toMatrix b b f - 1) i j ∈ I := by
    intro i j
    obtain ⟨s, hs⟩ := hf (b j)
    have : (LinearMap.toMatrix b b f - 1) i j = b.repr (f (b j) - b j) i := by
      simp [Matrix.sub_apply, LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    rw [this, hs, map_smul, Finsupp.smul_apply, smul_eq_mul, hI]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hdet : LinearMap.det f - 1 ∈ I := by
    rw [← LinearMap.det_toMatrix b]
    have hq : (Ideal.Quotient.mk I) (LinearMap.toMatrix b b f).det = (Ideal.Quotient.mk I) (1 : Matrix (Module.Free.ChooseBasisIndex ℤ_[p] T) (Module.Free.ChooseBasisIndex ℤ_[p] T) ℤ_[p]).det := by
      rw [RingHom.map_det, RingHom.map_det]
      congr 1
      ext i j
      have := hentry i j
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
      simpa [RingHom.mapMatrix_apply] using this
    rw [Matrix.det_one, map_one] at hq
    rw [← Ideal.Quotient.eq, hq, map_one]
  rw [hI, Ideal.mem_span_singleton] at hdet
  obtain ⟨c, hc⟩ := hdet
  rw [hc, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)

theorem norm_J (a : ℤ_[p]) : ‖((algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])) a‖ = ‖a‖ := by
  rw [RingHom.comp_apply, norm_algebraMap']
  simp

private theorem _root_.Ws47.U3.norm_p_cast : ‖((p : ℕ) : ℤ_[p])‖ = ‖((p : ℕ) : ℚ_[p])‖ := by
  rw [← PadicInt.padic_norm_e_of_padicInt]; norm_cast

p2m_export "Ws47.U3" "norm_p_cast"
theorem usub (x y : ℂ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

end Ws47.U3

namespace PadicComplex p2m_export "PadicComplex" "norm_extends Gal smul_coe norm_smul_eq smul_algebraMap" end PadicComplex
p2m_open_scoped "PadicComplex" in
open Ws47.U3 in

theorem PadicComplex.forall_smul_eq_det_mul_of_frobenius_decomposition_of_smul_eq_of_inertia_smul_eq_of_approx
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (ρ : (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) →* Module.End ℤ_[p] T)

    (hunr : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ρ τ = 1)

    (hcont : ∀ n : ℕ, ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K' ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ K'.fixingSubgroup →
          ∀ t : T, ∃ s : T, ρ τ t - t = ((p : ℤ_[p]) ^ n) • s)

    (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hφK : φ ∈ K.fixingSubgroup)
    (hdec : ∀ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M →
        ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
          ∃ (n : ℕ) (ι δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
            ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ ι ∈ K.fixingSubgroup ∧
            δ ∈ K.fixingSubgroup ∧ δ ∈ M.fixingSubgroup ∧
            σ = φ ^ n * ι * δ)

    (u : ℂ_[p]) (hu : ‖u‖ = 1)
    (hφu : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, (∀ t : PadicAlgCl p, τ t = φ t) →
      φ • u = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (LinearMap.det (ρ τ))) * u)
    (hιu : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι ∈ K.fixingSubgroup → ι • u = u)
    (happrox : ∀ k : ℕ, ∃ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M ∧
      ∃ m : PadicAlgCl p, m ∈ M ∧ ‖u - (m : ℂ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k) :
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
      (∀ t : PadicAlgCl p, τ t = σ t) →
      σ • u = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (LinearMap.det (ρ τ))) * u := by
  classical
  intro σ τ hτσ

  set J : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) with hJdef
  have hJ : ∀ a : ℤ_[p], algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] a) = J a := fun a => rfl
  simp only [hJ] at hφu ⊢
  have hJfix : ∀ (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℤ_[p]), γ • J a = J a := by
    intro γ a; rw [← hJ]; exact PadicComplex.smul_algebraMap p γ _
  have hiso : ∀ (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]), ‖γ • x‖ = ‖x‖ := PadicComplex.norm_smul_eq p
  have hσK : σ ∈ K.fixingSubgroup := mem_fixingSubgroup_of_agree p K hτσ
  set L := PadicAlgCl.ringOfIntegers.galToAlgEquiv p K with hL
  have hτ : τ = L ⟨σ, hσK⟩ := eq_galToAlgEquiv_of_agree p K hτσ
  have hφ' : φ • u = J (LinearMap.det (ρ (L ⟨φ, hφK⟩))) * u := hφu _ (fun t => rfl)
  set a := LinearMap.det (ρ (L ⟨φ, hφK⟩)) with ha
  have hφn : ∀ n : ℕ, φ ^ n • u = J a ^ n * u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, ih, smul_mul', hφ', ← map_pow, hJfix, map_pow]; ring

  suffices hk : ∀ k : ℕ, ‖σ • u - J (LinearMap.det (ρ τ)) * u‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k by
    have hp1 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
      rw [← norm_p_cast, PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have ht : Filter.Tendsto (fun k : ℕ => ‖((p : ℕ) : ℚ_[p])‖ ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp1
    have h0 : ‖σ • u - J (LinearMap.det (ρ τ)) * u‖ ≤ 0 := ge_of_tendsto' ht hk
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  intro k
  obtain ⟨K', hK'fd, hK'⟩ := hcont k
  obtain ⟨M₀, hM₀fd, m, hmM₀, hm⟩ := happrox k
  haveI := hK'fd
  haveI := hM₀fd
  haveI : FiniteDimensional ℚ_[p] ↥(K' ⊔ M₀) := IntermediateField.finiteDimensional_sup K' M₀
  obtain ⟨n, ι, δ, hιI, hιK, hδK, hδM, hσeq⟩ := hdec (K' ⊔ M₀) inferInstance σ hσK

  have hτeq : τ = L ⟨φ, hφK⟩ ^ n * L ⟨ι, hιK⟩ * L ⟨δ, hδK⟩ := by
    rw [hτ]
    have : (⟨σ, hσK⟩ : K.fixingSubgroup) = ⟨φ, hφK⟩ ^ n * ⟨ι, hιK⟩ * ⟨δ, hδK⟩ :=
      Subtype.ext (by simp [hσeq])
    rw [this, map_mul, map_mul, map_pow]
  have hρι : ρ (L ⟨ι, hιK⟩) = 1 := hunr ι (L ⟨ι, hιK⟩) (fun t => rfl) hιI
  have hdetτ : LinearMap.det (ρ τ) = a ^ n * LinearMap.det (ρ (L ⟨δ, hδK⟩)) := by
    simp only [hτeq, map_mul, map_pow, hρι, mul_one, ha]

  have hδK' : δ ∈ K'.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hδM ⊢
    intro x hx; exact hδM x ((le_sup_left : K' ≤ K' ⊔ M₀) hx)
  have hdetδ : ‖LinearMap.det (ρ (L ⟨δ, hδK⟩)) - 1‖ ≤ ‖((p : ℕ) : ℤ_[p])‖ ^ k :=
    norm_det_sub_one_le p (ρ (L ⟨δ, hδK⟩)) k (hK' δ (L ⟨δ, hδK⟩) (fun t => rfl) hδK')

  have hδm : δ • ((m : PadicAlgCl p) : ℂ_[p]) = ((m : PadicAlgCl p) : ℂ_[p]) := by
    rw [PadicComplex.smul_coe]
    congr 1
    rw [IntermediateField.mem_fixingSubgroup_iff] at hδM
    exact hδM m ((le_sup_right : M₀ ≤ K' ⊔ M₀) hmM₀)
  have h1 : ‖δ • u - u‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k := by
    have : δ • u - u = δ • (u - (m : ℂ_[p])) - (u - (m : ℂ_[p])) := by rw [smul_sub, hδm]; abel
    rw [this]
    calc ‖δ • (u - (m : ℂ_[p])) - (u - (m : ℂ_[p]))‖
        ≤ max ‖δ • (u - (m : ℂ_[p]))‖ ‖u - (m : ℂ_[p])‖ := usub p _ _
      _ = ‖u - (m : ℂ_[p])‖ := by rw [hiso, max_self]
      _ ≤ _ := hm
  have h2 : ‖σ • u - J a ^ n * u‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k := by
    rw [hσeq, mul_assoc, mul_smul, mul_smul, ← hφn n, ← smul_sub, hiso]
    calc ‖ι • δ • u - u‖ = ‖ι • (δ • u - u)‖ := by rw [smul_sub, hιu ι hιI hιK]
      _ = ‖δ • u - u‖ := hiso _ _
      _ ≤ _ := h1

  have h3 : ‖J (LinearMap.det (ρ τ)) * u - J a ^ n * u‖ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k := by
    rw [hdetτ, map_mul, map_pow, show J a ^ n * J (LinearMap.det (ρ (L ⟨δ, hδK⟩))) * u - J a ^ n * u
        = J a ^ n * (J (LinearMap.det (ρ (L ⟨δ, hδK⟩)) - 1)) * u by rw [map_sub, map_one]; ring,
      norm_mul, norm_mul, hu, mul_one, norm_pow]
    calc ‖J a‖ ^ n * ‖J (LinearMap.det (ρ (L ⟨δ, hδK⟩)) - 1)‖
        ≤ 1 ^ n * ‖((p : ℕ) : ℤ_[p])‖ ^ k := by
          apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by rw [norm_J]; exact PadicInt.norm_le_one a) n)
            (by rw [norm_J]; exact hdetδ) (norm_nonneg _) (by positivity)
      _ = ‖((p : ℕ) : ℚ_[p])‖ ^ k := by rw [one_pow, one_mul, norm_p_cast]

  calc ‖σ • u - J (LinearMap.det (ρ τ)) * u‖
      = ‖(σ • u - J a ^ n * u) - (J (LinearMap.det (ρ τ)) * u - J a ^ n * u)‖ := by congr 1; abel
    _ ≤ max ‖σ • u - J a ^ n * u‖ ‖J (LinearMap.det (ρ τ)) * u - J a ^ n * u‖ := usub p _ _
    _ ≤ ‖((p : ℕ) : ℚ_[p])‖ ^ k := max_le h2 h3

namespace Ws47
namespace UnitPeriod

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

omit [CompleteSpace L] in

theorem step (φ : L ≃+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) {r : ℝ}
    (hadd : ∀ c : L, ∃ y : L, ‖y‖ ≤ ‖c‖ ∧ ‖φ y - y - c‖ ≤ r * ‖c‖)
    {a u : L} (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (he1 : ‖φ u - a * u‖ < 1) :
    ∃ u' : L, ‖u'‖ = 1 ∧ ‖u' - u‖ ≤ ‖φ u - a * u‖ ∧
      ‖φ u' - a * u'‖ ≤ max r ‖φ u - a * u‖ * ‖φ u - a * u‖ := by
  set e : L := φ u - a * u with he
  have hau1 : ‖a * u‖ = 1 := by rw [norm_mul, ha, hu, one_mul]
  have hau : a * u ≠ 0 := fun h => by rw [h, norm_zero] at hau1; exact zero_ne_one hau1
  set c : L := -(e / (a * u)) with hc
  have hcn : ‖c‖ = ‖e‖ := by rw [hc, norm_neg, norm_div, hau1, div_one]
  obtain ⟨y, hy, hyc⟩ := hadd c
  have hy1 : ‖y‖ < 1 := (hy.trans_eq hcn).trans_lt he1
  have h1y : ‖1 + y‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : L)) (y := y)
      (by rw [norm_one]; exact (ne_of_gt hy1))
    rw [this, norm_one, max_eq_left hy1.le]
  refine ⟨u * (1 + y), by rw [norm_mul, hu, h1y, one_mul], ?_, ?_⟩
  · rw [show u * (1 + y) - u = u * y by ring, norm_mul, hu, one_mul]
    exact hy.trans_eq hcn
  ·
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hau
    have hu0 : u ≠ 0 := right_ne_zero_of_mul hau
    have key : φ (u * (1 + y)) - a * (u * (1 + y)) = a * u * (φ y - y - c) + e * φ y := by
      rw [map_mul, map_add, map_one, hc, he]
      field_simp
      ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_mul, hau1, one_mul, norm_mul, hφ y]
    refine max_le ?_ ?_
    · calc ‖φ y - y - c‖ ≤ r * ‖c‖ := hyc
        _ = r * ‖e‖ := by rw [hcn]
        _ ≤ max r ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · calc ‖e‖ * ‖y‖ ≤ ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_left (hy.trans_eq hcn) (norm_nonneg _)
        _ ≤ max r ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem exists_unit_period (φ : L ≃+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hadd : ∀ c : L, ∃ y : L, ‖y‖ ≤ ‖c‖ ∧ ‖φ y - y - c‖ ≤ r * ‖c‖)
    {a : L} (ha : ‖a‖ = 1) (hmul : ∃ y : L, ‖y‖ = 1 ∧ ‖φ y - a * y‖ < 1) :
    ∃ u : L, ‖u‖ = 1 ∧ φ u = a * u := by
  obtain ⟨u₀, hu₀, he₀⟩ := hmul
  set q : ℝ := max r ‖φ u₀ - a * u₀‖ with hq
  have hq0 : 0 ≤ q := hr0.trans (le_max_left _ _)
  have hq1 : q < 1 := max_lt hr1 he₀

  have hstep : ∀ u : {u : L // ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖},
      ∃ u' : {u : L // ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖},
        ‖u'.1 - u‖ ≤ ‖φ u - a * u‖ ∧ ‖φ u' - a * u'‖ ≤ q * ‖φ u - a * u‖ := by
    rintro ⟨u, hu, hue⟩
    obtain ⟨u', hu', hd, he'⟩ := step φ hφ hadd ha hu (hue.trans_lt he₀)
    have hq' : max r ‖φ u - a * u‖ ≤ q := max_le (le_max_left _ _) (hue.trans (le_max_right _ _))
    have he'' : ‖φ u' - a * u'‖ ≤ q * ‖φ u - a * u‖ := he'.trans (mul_le_mul_of_nonneg_right hq' (norm_nonneg _))
    refine ⟨⟨u', hu', ?_⟩, hd, he''⟩
    calc ‖φ u' - a * u'‖ ≤ q * ‖φ u - a * u‖ := he''
      _ ≤ 1 * ‖φ u - a * u‖ := mul_le_mul_of_nonneg_right hq1.le (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ _ := hue
  choose F hF using hstep
  let s : ℕ → {u : L // ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖} :=
    fun n => Nat.rec ⟨u₀, hu₀, le_rfl⟩ (fun _ x => F x) n
  have hs_succ : ∀ n, s (n + 1) = F (s n) := fun n => rfl

  have herr : ∀ n, ‖φ (s n).1 - a * (s n).1‖ ≤ q ^ n * ‖φ u₀ - a * u₀‖ := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      rw [hs_succ]
      calc _ ≤ q * ‖φ (s n).1 - a * (s n).1‖ := (hF (s n)).2
        _ ≤ q * (q ^ n * ‖φ u₀ - a * u₀‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (n + 1) * ‖φ u₀ - a * u₀‖ := by ring

  have hdist : ∀ n, dist (s n).1 (s (n + 1)).1 ≤ ‖φ u₀ - a * u₀‖ * q ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hs_succ]
    calc _ ≤ ‖φ (s n).1 - a * (s n).1‖ := (hF (s n)).1
      _ ≤ q ^ n * ‖φ u₀ - a * u₀‖ := herr n
      _ = _ := mul_comm _ _
  have hcauchy : CauchySeq fun n => (s n).1 := cauchySeq_of_le_geometric q ‖φ u₀ - a * u₀‖ hq1 hdist
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨u, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => ‖(s n).1‖) Filter.atTop (nhds ‖u‖) := (continuous_norm.tendsto _).comp hu
    have h2 : (fun n => ‖(s n).1‖) = fun _ => (1 : ℝ) := funext fun n => (s n).2.1
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  ·
    have hφi : Isometry φ := Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, dist_eq_norm, ← map_sub, hφ]
    have hcont : Continuous fun x : L => φ x - a * x := hφi.continuous.sub (continuous_const.mul continuous_id)
    have h1 : Filter.Tendsto (fun n => φ (s n).1 - a * (s n).1) Filter.atTop (nhds (φ u - a * u)) :=
      (hcont.tendsto u).comp hu
    have h2 : Filter.Tendsto (fun n => φ (s n).1 - a * (s n).1) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => herr n) ?_
      have : Filter.Tendsto (fun n => q ^ n * ‖φ u₀ - a * u₀‖) Filter.atTop (nhds (0 * ‖φ u₀ - a * u₀‖)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _
      simpa using this
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)

theorem exists_unit_period_mem_closure (φ : L ≃+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (S : Subfield L) (hS : ∀ x ∈ S, φ x ∈ S)
    (hadd : ∀ c ∈ S, ∃ y ∈ S, ‖y‖ ≤ ‖c‖ ∧ ‖φ y - y - c‖ ≤ r * ‖c‖)
    {a : L} (haS : a ∈ S) (ha : ‖a‖ = 1) (hmul : ∃ y ∈ S, ‖y‖ = 1 ∧ ‖φ y - a * y‖ < 1) :
    ∃ u : L, ‖u‖ = 1 ∧ φ u = a * u ∧ u ∈ closure (S : Set L) := by

  obtain ⟨u₀, hu₀S, hu₀, he₀⟩ := hmul
  set q : ℝ := max r ‖φ u₀ - a * u₀‖ with hq
  have hq0 : 0 ≤ q := hr0.trans (le_max_left _ _)
  have hq1 : q < 1 := max_lt hr1 he₀

  have hstepS : ∀ u : L, u ∈ S → ‖u‖ = 1 → ‖φ u - a * u‖ < 1 →
      ∃ u' : L, u' ∈ S ∧ ‖u'‖ = 1 ∧ ‖u' - u‖ ≤ ‖φ u - a * u‖ ∧
        ‖φ u' - a * u'‖ ≤ max r ‖φ u - a * u‖ * ‖φ u - a * u‖ := by
    intro u huS hu he1
    set e : L := φ u - a * u with he
    have heS : e ∈ S := S.sub_mem (hS u huS) (S.mul_mem haS huS)
    have hau1 : ‖a * u‖ = 1 := by rw [norm_mul, ha, hu, one_mul]
    have hau : a * u ≠ 0 := fun h => by rw [h, norm_zero] at hau1; exact zero_ne_one hau1
    set c : L := -(e / (a * u)) with hc
    have hcS : c ∈ S := S.neg_mem (S.div_mem heS (S.mul_mem haS huS))
    have hcn : ‖c‖ = ‖e‖ := by rw [hc, norm_neg, norm_div, hau1, div_one]
    obtain ⟨y, hyS, hy, hyc⟩ := hadd c hcS
    have hy1 : ‖y‖ < 1 := (hy.trans_eq hcn).trans_lt he1
    have h1y : ‖1 + y‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : L)) (y := y)
        (by rw [norm_one]; exact (ne_of_gt hy1))
      rw [this, norm_one, max_eq_left hy1.le]
    refine ⟨u * (1 + y), S.mul_mem huS (S.add_mem S.one_mem hyS), by rw [norm_mul, hu, h1y, one_mul], ?_, ?_⟩
    · rw [show u * (1 + y) - u = u * y by ring, norm_mul, hu, one_mul]
      exact hy.trans_eq hcn
    · have ha0 : a ≠ 0 := left_ne_zero_of_mul hau
      have hu0 : u ≠ 0 := right_ne_zero_of_mul hau
      have key : φ (u * (1 + y)) - a * (u * (1 + y)) = a * u * (φ y - y - c) + e * φ y := by
        rw [map_mul, map_add, map_one, hc, he]
        field_simp
        ring
      rw [key]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_mul, hau1, one_mul, norm_mul, hφ y]
      refine max_le ?_ ?_
      · calc ‖φ y - y - c‖ ≤ r * ‖c‖ := hyc
          _ = r * ‖e‖ := by rw [hcn]
          _ ≤ max r ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · calc ‖e‖ * ‖y‖ ≤ ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_left (hy.trans_eq hcn) (norm_nonneg _)
          _ ≤ max r ‖e‖ * ‖e‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hstep : ∀ u : {u : L // u ∈ S ∧ ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖},
      ∃ u' : {u : L // u ∈ S ∧ ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖},
        ‖(u'.1) - u.1‖ ≤ ‖φ u.1 - a * u.1‖ ∧ ‖φ u'.1 - a * u'.1‖ ≤ q * ‖φ u.1 - a * u.1‖ := by
    rintro ⟨u, huS, hu, hue⟩
    obtain ⟨u', hu'S, hu', hd, he'⟩ := hstepS u huS hu (hue.trans_lt he₀)
    have hq' : max r ‖φ u - a * u‖ ≤ q := max_le (le_max_left _ _) (hue.trans (le_max_right _ _))
    have he'' : ‖φ u' - a * u'‖ ≤ q * ‖φ u - a * u‖ := he'.trans (mul_le_mul_of_nonneg_right hq' (norm_nonneg _))
    refine ⟨⟨u', hu'S, hu', ?_⟩, hd, he''⟩
    calc ‖φ u' - a * u'‖ ≤ q * ‖φ u - a * u‖ := he''
      _ ≤ 1 * ‖φ u - a * u‖ := mul_le_mul_of_nonneg_right hq1.le (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ _ := hue
  choose F hF using hstep
  let s : ℕ → {u : L // u ∈ S ∧ ‖u‖ = 1 ∧ ‖φ u - a * u‖ ≤ ‖φ u₀ - a * u₀‖} :=
    fun n => Nat.rec ⟨u₀, hu₀S, hu₀, le_rfl⟩ (fun _ x => F x) n
  have hs_succ : ∀ n, s (n + 1) = F (s n) := fun n => rfl
  have herr : ∀ n, ‖φ (s n).1 - a * (s n).1‖ ≤ q ^ n * ‖φ u₀ - a * u₀‖ := by
    intro n
    induction n with
    | zero => simp [s]
    | succ n ih =>
      rw [hs_succ]
      calc _ ≤ q * ‖φ (s n).1 - a * (s n).1‖ := (hF (s n)).2
        _ ≤ q * (q ^ n * ‖φ u₀ - a * u₀‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (n + 1) * ‖φ u₀ - a * u₀‖ := by ring
  have hdist : ∀ n, dist (s n).1 (s (n + 1)).1 ≤ ‖φ u₀ - a * u₀‖ * q ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hs_succ]
    calc _ ≤ ‖φ (s n).1 - a * (s n).1‖ := (hF (s n)).1
      _ ≤ q ^ n * ‖φ u₀ - a * u₀‖ := herr n
      _ = _ := mul_comm _ _
  have hcauchy : CauchySeq fun n => (s n).1 := cauchySeq_of_le_geometric q ‖φ u₀ - a * u₀‖ hq1 hdist
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨u, ?_, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => ‖(s n).1‖) Filter.atTop (nhds ‖u‖) := (continuous_norm.tendsto _).comp hu
    have h2 : (fun n => ‖(s n).1‖) = fun _ => (1 : ℝ) := funext fun n => (s n).2.2.1
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  · have hφi : Isometry φ := Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, dist_eq_norm, ← map_sub, hφ]
    have hcont : Continuous fun x : L => φ x - a * x := hφi.continuous.sub (continuous_const.mul continuous_id)
    have h1 : Filter.Tendsto (fun n => φ (s n).1 - a * (s n).1) Filter.atTop (nhds (φ u - a * u)) :=
      (hcont.tendsto u).comp hu
    have h2 : Filter.Tendsto (fun n => φ (s n).1 - a * (s n).1) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => herr n) ?_
      have : Filter.Tendsto (fun n => q ^ n * ‖φ u₀ - a * u₀‖) Filter.atTop (nhds (0 * ‖φ u₀ - a * u₀‖)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _
      simpa using this
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  · exact mem_closure_of_tendsto hu (Filter.Eventually.of_forall fun n => (s n).2.1)

end Ws47.UnitPeriod

namespace Ws47
namespace U2I

variable (p : ℕ) [Fact p.Prime]

theorem norm_p_cast : ‖((p : ℕ) : ℤ_[p])‖ = ‖((p : ℕ) : ℚ_[p])‖ := by
  rw [← PadicInt.padic_norm_e_of_padicInt]; norm_cast

theorem usub (x y : ℂ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

noncomputable def S : Subfield ℂ_[p] :=
  (((IntermediateField.fixedField ((padicIntegers p).inertiaSubgroupIn ℚ_[p])).toSubfield).map
        (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]))

theorem smul_mem_S (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : ℂ_[p]} (hx : x ∈ S p) : γ • x ∈ S p := by
  obtain ⟨y, hy, rfl⟩ := Subfield.mem_map.1 hx
  have hy' : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι y = y :=
    fun ι hι => (IntermediateField.mem_fixedField_iff _ _).1 hy ι hι
  refine Subfield.mem_map.2 ⟨γ y, ?_, ?_⟩
  · show γ y ∈ IntermediateField.fixedField _
    rw [IntermediateField.mem_fixedField_iff]
    intro ι hι
    have hconj : γ⁻¹ * ι * γ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
      have := (PadicAlgCl.inertiaSubgroupIn_normal p).conj_mem ι hι γ⁻¹
      simpa using this
    have := hy' _ hconj
    simp only [AlgEquiv.mul_apply] at this
    calc ι (γ y) = γ (γ⁻¹ (ι (γ y))) := by simp
      _ = γ y := by rw [this]
  · change ((γ y : PadicAlgCl p) : ℂ_[p]) = γ • ((y : PadicAlgCl p) : ℂ_[p])
    rw [PadicComplex.smul_coe]

theorem mem_S_iff (x : ℂ_[p]) : x ∈ S p ↔ ∃ y : PadicAlgCl p,
    (∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι y = y) ∧ (y : ℂ_[p]) = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subfield.mem_map.1 hx
    exact ⟨y, fun ι hι => (IntermediateField.mem_fixedField_iff _ _).1 hy ι hι, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Subfield.mem_map.2 ⟨y, (IntermediateField.mem_fixedField_iff _ _).2 (fun ι hι => hy ι hι), rfl⟩

theorem exists_norm_eq_of_mem_S {x : ℂ_[p]} (hx : x ∈ S p) (hx0 : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖(p : ℚ_[p])‖ ^ n := by
  obtain ⟨y, hy, rfl⟩ := (mem_S_iff p _).1 hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hx0
  obtain ⟨n, hn⟩ := PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self p hy0 hy
  refine ⟨n, ?_⟩
  rw [show ‖((y : PadicAlgCl p) : ℂ_[p])‖ = ‖y‖ from UniformSpace.Completion.norm_coe y, hn]
  congr 1
  rw [show (p : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) by simp, norm_algebraMap']

section OmegaHelpers

variable {p}

open UniformSpace

theorem hp' : p.Prime := Fact.out

theorem norm_natCast_p_algCl : ‖(p : PadicAlgCl p)‖ = ‖(p : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap']

theorem norm_p_lt_one' : ‖(p : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_natCast_lt_one_iff]

theorem natCast_p_ne_zero : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.mpr hp'.ne_zero

theorem inertia_fix_of_teich {y : PadicAlgCl p} (hy : y = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) :
    ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι y = y := by
  intro ι hι
  rcases hy with rfl | ⟨m, hm, hym⟩
  · exact map_zero ι
  · exact PadicAlgCl.apply_eq_self_of_forall_norm_sub_lt_one_of_pow_eq_one_of_coprime p ι
      ((PadicAlgCl.mem_inertiaSubgroupIn_iff_forall_norm_sub_lt_one p ι).mp hι) hm hym

theorem norm_le_one_of_teich {y : PadicAlgCl p} (hy : y = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) : ‖y‖ ≤ 1 := by
  rcases hy with rfl | ⟨m, hm, hym⟩
  · simp
  · have hm0 : m ≠ 0 := by rintro rfl; exact hp'.ne_one (Nat.Coprime.eq_one_of_dvd hm (dvd_zero p))
    have h := congrArg norm hym
    rw [norm_pow, norm_one] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp h).le

theorem inertia_fix_map (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {y : PadicAlgCl p}
    (hy : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι y = y) :
    ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι (φ y) = φ y := by
  intro ι hι
  haveI := PadicAlgCl.inertiaSubgroupIn_normal p
  have hconj : φ⁻¹ * ι * φ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
    have := Subgroup.Normal.conj_mem inferInstance ι hι φ⁻¹
    simpa using this
  have h := hy _ hconj
  have : φ ((φ⁻¹ * ι * φ) y) = φ y := by rw [h]
  simpa [AlgEquiv.mul_apply] using this

theorem norm_le_norm_p_of_lt_one {w : PadicAlgCl p}
    (hw : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι w = w)
    (h1 : ‖w‖ < 1) : ‖w‖ ≤ ‖(p : ℚ_[p])‖ := by
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; exact norm_nonneg _
  obtain ⟨n, hn⟩ := PadicAlgCl.exists_norm_eq_norm_pow_of_forall_inertia_apply_eq_self p hw0 hw
  rw [norm_natCast_p_algCl] at hn
  rw [hn] at h1 ⊢
  have hr0 : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp'.ne_zero)
  have hr1 : ‖(p : ℚ_[p])‖ < 1 := norm_p_lt_one'
  have hn1 : 1 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : (1 : ℝ) ≤ ‖(p : ℚ_[p])‖ ^ n := by
      rw [← zpow_zero ‖(p : ℚ_[p])‖]
      exact zpow_le_zpow_right_of_le_one₀ hr0 hr1.le (by omega)
    exact absurd (lt_of_le_of_lt this h1) (lt_irrefl _)
  calc ‖(p : ℚ_[p])‖ ^ n ≤ ‖(p : ℚ_[p])‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hn1
    _ = ‖(p : ℚ_[p])‖ := zpow_one _

end OmegaHelpers

theorem hadd (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : ℕ) (hf : 0 < f)
    (hfrob : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1) :
    ∀ c ∈ S p, ∃ y ∈ S p, ‖y‖ ≤ ‖c‖ ∧ ‖(MulSemiringAction.toRingEquiv (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] φ) y - y - c‖ ≤ ‖(p : ℚ_[p])‖ * ‖c‖ := by
  classical
  intro c hc
  by_cases hc0 : c = 0
  · refine ⟨0, (S p).zero_mem, by rw [hc0], ?_⟩
    rw [map_zero, sub_zero, hc0, sub_zero, norm_zero, mul_zero]

  obtain ⟨c₁, hc₁fix, rfl⟩ := (mem_S_iff p _).mp hc
  obtain ⟨n, hn⟩ := exists_norm_eq_of_mem_S p hc hc0
  set r : ℝ := ‖(p : ℚ_[p])‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp'.ne_zero)
  have hpn : ‖(p : PadicAlgCl p) ^ n‖ = r ^ n := by rw [norm_zpow, norm_natCast_p_algCl]
  have hc₁n : ‖c₁‖ = r ^ n := by rw [← PadicComplex.norm_extends p c₁]; exact hn

  set c₀ : PadicAlgCl p := c₁ * ((p : PadicAlgCl p) ^ n)⁻¹ with hc₀
  have hc₀c₁ : c₁ = c₀ * (p : PadicAlgCl p) ^ n := by
    rw [hc₀, inv_mul_cancel_right₀ (zpow_ne_zero n natCast_p_ne_zero)]
  have hc₀n : ‖c₀‖ = 1 := by
    rw [hc₀, norm_mul, norm_inv, hpn, hc₁n, mul_inv_cancel₀ (zpow_ne_zero n hr0.ne')]
  have hc₀fix : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι c₀ = c₀ :=
    fun ι hι => by rw [hc₀, map_mul, map_inv₀, map_zpow₀, map_natCast, hc₁fix ι hι]

  set q : ℕ := p ^ f with hq
  have hpq : p ∣ q := dvd_pow_self p hf.ne'
  have h1q : 1 < q := Nat.one_lt_pow hf.ne' hp'.one_lt
  obtain ⟨y₀, hy₀, hAS⟩ :=
    (PadicAlgCl.exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang p).2.1 q hpq h1q c₀ hc₀n.le
  have hy₀n : ‖y₀‖ ≤ 1 := norm_le_one_of_teich hy₀
  have hy₀fix := inertia_fix_of_teich hy₀

  set w : PadicAlgCl p := φ y₀ - y₀ - c₀ with hw
  have hwlt : ‖w‖ < 1 := by
    have : w = (φ y₀ - y₀ ^ q) + (y₀ ^ q - y₀ - c₀) := by rw [hw]; ring
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hfrob y₀ hy₀n) hAS)
  have hwfix : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι w = w :=
    fun ι hι => by rw [hw, map_sub, map_sub, inertia_fix_map φ hy₀fix ι hι, hy₀fix ι hι, hc₀fix ι hι]
  have hwle : ‖w‖ ≤ r := norm_le_norm_p_of_lt_one hwfix hwlt

  set y₁ : PadicAlgCl p := y₀ * (p : PadicAlgCl p) ^ n with hy₁
  have hy₁fix : ∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι y₁ = y₁ :=
    fun ι hι => by rw [hy₁, map_mul, map_zpow₀, map_natCast, hy₀fix ι hι]
  refine ⟨(y₁ : ℂ_[p]), (mem_S_iff p _).mpr ⟨y₁, hy₁fix, rfl⟩, ?_, ?_⟩
  · rw [PadicComplex.norm_extends, hn, hy₁, norm_mul, hpn]
    exact mul_le_of_le_one_left (zpow_nonneg hr0.le _) hy₀n
  · rw [MulSemiringAction.toRingEquiv_apply, PadicComplex.smul_coe, ← UniformSpace.Completion.coe_sub,
      ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, hn]
    have : φ y₁ - y₁ - c₁ = w * (p : PadicAlgCl p) ^ n := by
      rw [hy₁, hc₀c₁, hw, map_mul, map_zpow₀, map_natCast]; ring
    rw [this, norm_mul, hpn]
    exact mul_le_mul_of_nonneg_right hwle (zpow_nonneg hr0.le _)

theorem hmul (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : ℕ) (hf : 0 < f)
    (hfrob : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1) (a : ℤ_[p]ˣ) :
    ∃ y ∈ S p, ‖y‖ = 1 ∧ ‖(MulSemiringAction.toRingEquiv (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] φ) y - (algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p]))) * y‖ < 1 := by
  classical
  set a₁ : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])) with ha₁
  have ha₁n : ‖a₁‖ = 1 := by
    rw [ha₁, norm_algebraMap', show (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])) = ((a : ℤ_[p]) : ℚ_[p]) from rfl,
      PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.isUnit_iff.mp a.isUnit
  set q : ℕ := p ^ f with hq
  have hpq : p ∣ q := dvd_pow_self p hf.ne'
  have h1q : 1 < q := Nat.one_lt_pow hf.ne' hp'.one_lt
  obtain ⟨y₀, hy₀, hL⟩ :=
    (PadicAlgCl.exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang p).2.2 q hpq h1q a₁ ha₁n
  obtain ⟨m, hm, hym⟩ := hy₀
  have hm0 : m ≠ 0 := by rintro rfl; exact hp'.ne_one (Nat.Coprime.eq_one_of_dvd hm (dvd_zero p))
  have hy₀n : ‖y₀‖ = 1 := by
    have h := congrArg norm hym
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp h
  have hy₀fix := inertia_fix_of_teich (Or.inr ⟨m, hm, hym⟩)
  refine ⟨(y₀ : ℂ_[p]), (mem_S_iff p _).mpr ⟨y₀, hy₀fix, rfl⟩, by rw [PadicComplex.norm_extends, hy₀n], ?_⟩
  have hJ : algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])) = (a₁ : ℂ_[p]) := rfl
  rw [MulSemiringAction.toRingEquiv_apply, PadicComplex.smul_coe, hJ, ← UniformSpace.Completion.coe_mul,
    ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends]
  have hq1 : 1 ≤ q := h1q.le
  have : φ y₀ - a₁ * y₀ = (φ y₀ - y₀ ^ q) + y₀ * (y₀ ^ (q - 1) - a₁) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel hq1]; ring
  rw [this]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hfrob y₀ hy₀n.le) ?_)
  rw [norm_mul, hy₀n, one_mul]
  exact hL

theorem approx_of_mem_closure {u : ℂ_[p]} (hu : u ∈ closure (S p : Set ℂ_[p])) :
    (∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι • u = u) ∧
    ∀ k : ℕ, ∃ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M ∧
      ∃ m : PadicAlgCl p, m ∈ M ∧ ‖u - (m : ℂ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k := by
  have hp0 : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

  have key : ∀ k : ℕ, ∃ m : PadicAlgCl p,
      (∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι m = m) ∧
      ‖u - (m : ℂ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k := by
    intro k
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hu (‖(p : ℚ_[p])‖ ^ k) (pow_pos hp0 k)
    obtain ⟨m, hm, rfl⟩ := (mem_S_iff p b).1 hb
    exact ⟨m, hm, by rw [← dist_eq_norm]; exact hdist.le⟩
  refine ⟨?_, ?_⟩
  · intro ι hι
    have hk : ∀ k : ℕ, ‖ι • u - u‖ ≤ ‖(p : ℚ_[p])‖ ^ k := by
      intro k
      obtain ⟨m, hm, hum⟩ := key k
      have hιm : ι • ((m : PadicAlgCl p) : ℂ_[p]) = ((m : PadicAlgCl p) : ℂ_[p]) := by
        rw [PadicComplex.smul_coe, hm ι hι]
      have : ι • u - u = ι • (u - (m : ℂ_[p])) - (u - (m : ℂ_[p])) := by rw [smul_sub, hιm]; abel
      rw [this]
      calc ‖ι • (u - (m : ℂ_[p])) - (u - (m : ℂ_[p]))‖
          ≤ max ‖ι • (u - (m : ℂ_[p]))‖ ‖u - (m : ℂ_[p])‖ := usub p _ _
        _ = ‖u - (m : ℂ_[p])‖ := by rw [PadicComplex.norm_smul_eq, max_self]
        _ ≤ _ := hum
    have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
      rw [← norm_p_cast p, PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have ht : Filter.Tendsto (fun k : ℕ => ‖(p : ℚ_[p])‖ ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' ht hk))
  · intro k
    obtain ⟨m, hm, hum⟩ := key k
    have hint : IsIntegral ℚ_[p] m := Algebra.IsIntegral.isIntegral m
    exact ⟨IntermediateField.adjoin ℚ_[p] {m}, IntermediateField.adjoin.finiteDimensional hint, m,
      IntermediateField.mem_adjoin_simple_self ℚ_[p] m, hum⟩

theorem exists_unit_period_padicComplex
    (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : ℕ) (hf : 0 < f)
    (hfrob : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1)
    (a : ℤ_[p]ˣ) :
    ∃ u : ℂ_[p], ‖u‖ = 1 ∧
      φ • u = (algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p]))) * u ∧
      (∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι • u = u) ∧
      ∀ k : ℕ, ∃ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M ∧
        ∃ m : PadicAlgCl p, m ∈ M ∧ ‖u - (m : ℂ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k := by
  classical
  have hp0 : 0 ≤ ‖(p : ℚ_[p])‖ := norm_nonneg _
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [← Ws47.U2I.norm_p_cast p, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  set φL := MulSemiringAction.toRingEquiv (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] φ with hφLdef
  have hφL : ∀ x, ‖φL x‖ = ‖x‖ := fun x => PadicComplex.norm_smul_eq p φ x

  have hJa : (algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p]))) = (((algebraMap ℤ_[p] (PadicAlgCl p) (a : ℤ_[p])) : PadicAlgCl p) : ℂ_[p]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
    rfl
  have haS : (algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p]))) ∈ S p := by
    rw [hJa, mem_S_iff]
    refine ⟨_, fun ι _ => ?_, rfl⟩
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact ι.commutes _
  have ha : ‖(algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])))‖ = 1 := by
    rw [norm_algebraMap', show ‖algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])‖ = ‖(a : ℤ_[p])‖ from PadicInt.padic_norm_e_of_padicInt _]
    exact PadicInt.isUnit_iff.1 a.isUnit
  obtain ⟨u, hu1, hφu, hcl⟩ := Ws47.UnitPeriod.exists_unit_period_mem_closure φL hφL hp0 hp1 (S p)
    (fun x hx => smul_mem_S p φ hx) (hadd p φ f hf hfrob) haS ha (hmul p φ f hf hfrob a)
  obtain ⟨hι, happ⟩ := approx_of_mem_closure p hcl
  exact ⟨u, hu1, hφu, hι, happ⟩

end Ws47.U2I

namespace Ws47
namespace C4A

private theorem _root_.Ws47.C4A.exists_unit_period_padicComplex
    (p : ℕ) [Fact p.Prime] (φ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : ℕ) (hf : 0 < f)
    (hfrob : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖φ x - x ^ (p ^ f)‖ < 1)
    (a : ℤ_[p]ˣ) :
    ∃ u : ℂ_[p], ‖u‖ = 1 ∧
      φ • u = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p])) * u ∧
      (∀ ι : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ι ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ι • u = u) ∧
      ∀ k : ℕ, ∃ (M : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] M ∧
        ∃ m : PadicAlgCl p, m ∈ M ∧ ‖u - (m : ℂ_[p])‖ ≤ ‖(p : ℚ_[p])‖ ^ k :=
  Ws47.U2I.exists_unit_period_padicComplex p φ f hf hfrob a

p2m_export "Ws47.C4A" "exists_unit_period_padicComplex"

theorem isUnit_det {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (ρ : (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) →* Module.End ℤ_[p] T) (τ) :
    IsUnit (LinearMap.det (ρ τ)) :=
  (ρ.toHomUnits τ).isUnit.map LinearMap.det

end Ws47.C4A

open Ws47.C4A in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (ρ : (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) →* Module.End ℤ_[p] T)

    (hunr : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ρ τ = 1)

    (hcont : ∀ n : ℕ, ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K' ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ K'.fixingSubgroup →
          ∀ t : T, ∃ s : T, ρ τ t - t = ((p : ℤ_[p]) ^ n) • s) :
    ∃ u : ℂ_[p], u ≠ 0 ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ • u = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (LinearMap.det (ρ τ))) * u := by
  classical
  obtain ⟨f, φ, hf, hφK, hfrob, hdec⟩ :=
    PadicAlgCl.exists_frobeniusLift_forall_eq_pow_mul_inertia_mul_of_finiteDimensional p K
  set L := PadicAlgCl.ringOfIntegers.galToAlgEquiv p K
  obtain ⟨a, ha⟩ := isUnit_det ρ (L ⟨φ, hφK⟩)
  obtain ⟨u, hu1, hφu, hιu, happrox⟩ := exists_unit_period_padicComplex p φ f hf hfrob a
  refine ⟨u, fun h0 => by simp [h0] at hu1, ?_⟩
  refine PadicComplex.forall_smul_eq_det_mul_of_frobenius_decomposition_of_smul_eq_of_inertia_smul_eq_of_approx
    p K ρ hunr hcont φ hφK hdec u hu1 ?_ (fun ι hι _ => hιu ι hι) happrox
  intro τ hτ
  have : τ = L ⟨φ, hφK⟩ := Ws47.U3.eq_galToAlgEquiv_of_agree p K hτ
  rw [this, ← ha]; exact hφu

end S_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
end P2MW
export P2MW.S_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers (solution)
