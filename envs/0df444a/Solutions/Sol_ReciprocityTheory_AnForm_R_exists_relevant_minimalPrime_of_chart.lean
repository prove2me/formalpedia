-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_relevant_minimalPrime_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:49.222594+00:00
-- url     : https://prove2.me/submissions/fff7bd61-05f9-42ae-a79d-be4296e53115

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypB
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__smul_of_isMultiHomog__a1eea59a9f1b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k)
    (M : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hM : M ∈ (chartIdeal P p).minimalPrimes)
    (hDM : D ≤ M) :
    ∃ q ∈ P.minimalPrimes, IsRelevant q ∧ D ≤ q := by
  classical
  set R := MvPolynomial (Σ k, ι k) ℂ
  have hMp : M.IsPrime := hM.1.1
  have hcM : chartIdeal P p ≤ M := hM.1.2
  have hX1 : ∀ k, (X ⟨k, p k⟩ - 1 : R) ∈ M := fun k =>
    hcM (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXM : ∀ k, (X ⟨k, p k⟩ : R) ∉ M := fun k h =>
    hMp.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := M.sub_mem h (hX1 k); simpa using this))
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hcM : P ≤ M)
  have hqp : q.IsPrime := hq.1.1
  have hPq : P ≤ q := hq.1.2
  set s : R := ∏ k, X ⟨k, p k⟩
  have hsq : s ∉ q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := q)).mp h
    exact hXM k (hqM hk)
  have hdis : Disjoint (Submonoid.powers s : Set R) ↑q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hsq
  let A := Localization.Away s
  have hu : ∀ k, IsUnit (algebraMap R A (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (algebraMap R A)
      (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : R)) (Finset.mem_univ k)))
      (IsLocalization.Away.algebraMap_isUnit (S := A) s)
  let u : K → A := fun k => ((hu k).unit⁻¹ : Aˣ)
  have hu1 : ∀ k, u k * algebraMap R A (X ⟨k, p k⟩) = 1 := fun k => (hu k).val_inv_mul
  let σ : R →+* A := eval₂Hom (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r))
  have hσ : ∀ (f : R) (a : K → ℕ), IsMultiHomog f a →
      σ f = (∏ k, u k ^ a k) * algebraMap R A f := by
    intro f a hf
    show eval₂ (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r)) f = _
    rw [eval₂_smul_of_isMultiHomog' (algebraMap ℂ A) hf u (fun r => algebraMap R A (X r))]
    congr 1
    conv_rhs => rw [← eval₂_eta f, eval₂_comp_left]
    congr 1
  let Q : Ideal A := Ideal.map (algebraMap R A) q
  have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) A q hqp hdis
  have hQq : Q.comap (algebraMap R A) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) A hqp hdis
  let M' : Ideal R := Q.comap σ
  have : M'.IsPrime := Ideal.comap_isPrime σ Q

  have hs1 : IsUnit (Ideal.Quotient.mk M s) := by
    have : ∀ k, Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := fun k => by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    simp [s, map_prod, this]
  let φ : A →+* R ⧸ M := IsLocalization.Away.lift s hs1
  have hφa : ∀ x : R, φ (algebraMap R A x) = Ideal.Quotient.mk M x := fun x =>
    IsLocalization.Away.lift_eq s hs1 x
  have hφu : ∀ k, φ (u k) = 1 := fun k => by
    have h := congrArg φ (hu1 k)
    rw [map_mul, map_one, hφa] at h
    have hx : Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    rw [hx, mul_one] at h; exact h
  have hφσ : φ.comp σ = Ideal.Quotient.mk M := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [σ, IsScalarTower.algebraMap_apply ℂ R A, hφa]; rfl
    · intro r
      simp [σ, hφa, hφu]
  have hM'M : M' ≤ M := by
    intro g hg
    have hQ : Q ≤ (⊥ : Ideal (R ⧸ M)).comap φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hφa, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hqM hx
    have h0 := hQ hg
    simp only [Ideal.mem_comap, Ideal.mem_bot] at h0
    have : Ideal.Quotient.mk M g = 0 := by rw [← hφσ]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hcM' : chartIdeal P p ≤ M' := by
    refine sup_le ?_ ?_
    · obtain ⟨S, hS, hPS⟩ := hP
      rw [hPS, Ideal.span_le]
      intro f hfS
      obtain ⟨a, ha⟩ := hS f hfS
      show σ f ∈ Q
      rw [hσ f a ha]
      exact Q.mul_mem_left _ (Ideal.mem_map_of_mem _ (hPq (hPS ▸ Ideal.subset_span hfS)))
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show σ _ ∈ Q
      have : σ (X ⟨k, p k⟩ - 1) = 0 := by
        have hσX : σ (X ⟨k, p k⟩) = u k * algebraMap R A (X ⟨k, p k⟩) := eval₂_X _ _ _
        rw [map_sub, map_one, hσX, hu1, sub_self]
      rw [this]; exact Q.zero_mem
  have hMM' : M ≤ M' := hM.2 ⟨inferInstance, hcM'⟩ hM'M
  refine ⟨q, hq, fun k => ⟨p k, fun h => hXM k (hqM h)⟩, ?_⟩
  obtain ⟨T, hT, hDT⟩ := hD
  rw [hDT, Ideal.span_le]
  intro f hfT
  obtain ⟨a, ha⟩ := hT f hfT
  have hfM' : σ f ∈ Q := hMM' (hDM (hDT ▸ Ideal.subset_span hfT))
  rw [hσ f a ha] at hfM'
  have hunit : IsUnit (∏ k, u k ^ a k) :=
    IsUnit.prod_univ_iff.mpr fun k => ((hu k).unit⁻¹).isUnit.pow _
  have : algebraMap R A f ∈ Q := by
    have := Q.mul_mem_left (hunit.unit⁻¹ : Aˣ).1 hfM'
    rwa [← mul_assoc, hunit.val_inv_mul, one_mul] at this
  rw [← hQq]; exact this
end ReciprocityTheory.AnForm.R
