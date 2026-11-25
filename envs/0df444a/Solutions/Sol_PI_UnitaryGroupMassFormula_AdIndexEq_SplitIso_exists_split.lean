-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:39.435871+00:00
-- url     : https://prove2.me/submissions/7131ece8-c823-4960-bfc3-5a408953874f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_sigT_algebraMap
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_sigT_tmul_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_exists_alpha
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
variable (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0)
include hσσ hfix h2 h2K
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
theorem _root_.solution (hnf : ¬ IsField (K ⊗[F] E)) :
    ∃ π : K ⊗[F] E ≃+* K × K, ∀ r, π (sigT σ r) = (π r).swap := by
  have h2F : (2 : F) ≠ 0 := by
    intro h
    apply h2K
    have := congrArg (algebraMap F K) h
    rwa [map_ofNat, map_zero] at this
  obtain ⟨α, hα0, hσα⟩ := exists_alpha σ hσσ hfix h2

  have hli : LinearIndependent F ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσα, map_zero, smul_neg] at h'
    have ht : (2 * t) • α = 0 := by
      rw [mul_smul, two_smul]
      linear_combination hst - h'
    have ht0 : t = 0 := by
      rcases smul_eq_zero.1 ht with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2F
      · exact absurd h hα0
    subst ht0
    refine ⟨?_, rfl⟩
    simpa using hst
  let bE : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hbE0 : bE 0 = 1 := by simp [bE]
  have hbE1 : bE 1 = α := by simp [bE]
  let bR : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K bE
  set A : K ⊗[F] E := (1 : K) ⊗ₜ[F] α with hAdef
  have hbR0 : bR 0 = 1 := by
    simp [bR, Algebra.TensorProduct.basis_apply, hbE0, Algebra.TensorProduct.one_def]
  have hbR1 : bR 1 = A := by
    simp [bR, Algebra.TensorProduct.basis_apply, hbE1, hAdef]
  have hdec : ∀ r : K ⊗[F] E, ∃ x y : K,
      r = algebraMap K (K ⊗[F] E) x + algebraMap K (K ⊗[F] E) y * A := by
    intro r
    refine ⟨bR.repr r 0, bR.repr r 1, ?_⟩
    conv_lhs => rw [← bR.sum_repr r]
    rw [Fin.sum_univ_two, hbR0, hbR1, Algebra.smul_def, Algebra.smul_def, mul_one]

  obtain ⟨b0, hb0⟩ := hfix (α * α) (by rw [map_mul, hσα]; ring)
  have hb00 : b0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb0
    exact hα0 (mul_self_eq_zero.1 hb0.symm)
  set bK : K := algebraMap F K b0 with hbK
  have hbK0 : bK ≠ 0 := by
    rw [hbK]; exact (map_ne_zero _).2 hb00
  have hA : A * A = algebraMap K (K ⊗[F] E) bK := by
    rw [hAdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb0, Algebra.TensorProduct.algebraMap_apply, hbK,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    rw [smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]
  have hnt : (1 : K ⊗[F] E) ≠ 0 := by
    rw [← hbR0]; exact bR.ne_zero 0

  have hsq : ∃ c : K, c * c = bK := by
    by_contra hno
    push Not at hno
    apply hnf
    refine ⟨⟨0, 1, hnt.symm⟩, mul_comm, ?_⟩
    intro r hr
    obtain ⟨x, y, rfl⟩ := hdec r
    set N : K := x * x - bK * y * y with hN
    have hN0 : N ≠ 0 := by
      intro h0
      by_cases hy : y = 0
      · subst hy
        have hx : x = 0 := by simpa [hN] using h0
        subst hx
        exact hr (by simp)
      · apply hno (x / y)
        field_simp
        linear_combination h0
    refine ⟨algebraMap K (K ⊗[F] E) N⁻¹ *
      (algebraMap K (K ⊗[F] E) x - algebraMap K (K ⊗[F] E) y * A), ?_⟩
    have hNN : algebraMap K (K ⊗[F] E) N⁻¹ *
        (algebraMap K (K ⊗[F] E) x * algebraMap K (K ⊗[F] E) x -
          algebraMap K (K ⊗[F] E) bK * algebraMap K (K ⊗[F] E) y * algebraMap K (K ⊗[F] E) y) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_mul, ← hN, inv_mul_cancel₀ hN0, map_one]
    linear_combination (-(algebraMap K (K ⊗[F] E) N⁻¹ * algebraMap K (K ⊗[F] E) y *
      algebraMap K (K ⊗[F] E) y)) * hA + hNN
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hbK0 (by simpa using hc.symm)
  set ac := algebraMap K (K ⊗[F] E) c
  set aci := algebraMap K (K ⊗[F] E) c⁻¹
  set a2i := algebraMap K (K ⊗[F] E) (2⁻¹ : K)
  have hci : aci * ac = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have h2i : a2i * 2 = 1 := by
    have : a2i * algebraMap K (K ⊗[F] E) 2 = 1 := by rw [← map_mul, inv_mul_cancel₀ h2K, map_one]
    rwa [map_ofNat] at this
  have hcc : ac * ac = algebraMap K (K ⊗[F] E) bK := by rw [← map_mul, hc]
  obtain ⟨e, he⟩ : ∃ e : K ⊗[F] E, e = a2i * (1 + aci * A) := ⟨_, rfl⟩
  have hee : e * e = e := by
    rw [he]
    linear_combination (a2i ^ 2 * aci ^ 2) * hA - (a2i ^ 2 * aci ^ 2) * hcc +
      (a2i ^ 2 * (aci * ac + 1)) * hci + ((1 + aci * A) * a2i) * h2i
  have hsA : sigT σ A = -A := by
    rw [hAdef, sigT_tmul_one, hσα, TensorProduct.tmul_neg]
  have hse : sigT σ e = 1 - e := by
    rw [he, map_mul, map_add, map_one, map_mul, hsA]
    simp only [a2i, aci, sigT_algebraMap]
    linear_combination h2i

  let ψ : K × K →+* K ⊗[F] E :=
    { toFun := fun p => algebraMap K (K ⊗[F] E) p.1 * e + algebraMap K (K ⊗[F] E) p.2 * (1 - e)
      map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one]; ring
      map_mul' := by
        intro p q
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(algebraMap K (K ⊗[F] E) p.1 - algebraMap K (K ⊗[F] E) p.2) *
          (algebraMap K (K ⊗[F] E) q.1 - algebraMap K (K ⊗[F] E) q.2)) * hee
      map_zero' := by simp
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hψ : ∀ p, ψ p = algebraMap K (K ⊗[F] E) p.1 * e + algebraMap K (K ⊗[F] E) p.2 * (1 - e) :=
    fun p => rfl
  have he0 : e ≠ 0 := by
    intro h0
    have := hse
    rw [h0, map_zero, sub_zero] at this
    exact hnt this.symm
  have he1 : 1 - e ≠ 0 := by
    intro h0
    have h1 : e = 1 := by linear_combination -h0
    have := hse
    rw [h1, map_one, sub_self] at this
    exact hnt this
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hψ] at hp
    have h1 : algebraMap K (K ⊗[F] E) p.1 * e = 0 := by
      have := congrArg (· * e) hp
      simp only [zero_mul] at this
      linear_combination this - (algebraMap K (K ⊗[F] E) p.1 - algebraMap K (K ⊗[F] E) p.2) * hee
    have h2' : algebraMap K (K ⊗[F] E) p.2 * (1 - e) = 0 := by
      linear_combination hp - h1
    rw [← Algebra.smul_def] at h1 h2'
    have e1 := (smul_eq_zero.1 h1).resolve_right he0
    have e2 := (smul_eq_zero.1 h2').resolve_right he1
    exact Prod.ext e1 e2
  have hsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨x, y, rfl⟩ := hdec r
    refine ⟨(x + y * c, x - y * c), ?_⟩
    rw [hψ, he]
    simp only [map_add, map_sub, map_mul]
    linear_combination (algebraMap K (K ⊗[F] E) y * (ac - A) + 2 * algebraMap K (K ⊗[F] E) y * A) * h2i +
      (2 * algebraMap K (K ⊗[F] E) y * a2i * A) * hci
  let Ψ : K × K ≃+* K ⊗[F] E := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  refine ⟨Ψ.symm, ?_⟩
  intro r
  obtain ⟨p, rfl⟩ := hsurj r
  have : sigT σ (ψ p) = ψ p.swap := by
    rw [hψ, hψ, map_add, map_mul, map_mul, sigT_algebraMap, sigT_algebraMap, map_sub, map_one, hse]
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have hΨ : ∀ q, Ψ.symm (ψ q) = q := fun q => Ψ.symm_apply_apply q
  rw [this, hΨ, hΨ]
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
