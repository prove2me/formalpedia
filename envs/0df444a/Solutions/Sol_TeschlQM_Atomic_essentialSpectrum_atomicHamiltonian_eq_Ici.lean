-- Prove2me | solution 1 for TeschlQM.Atomic.essentialSpectrum_atomicHamiltonian_eq_Ici
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:57:19.220982+00:00
-- url     : https://prove2.me/submissions/84efb9bb-2824-4460-9142-ea7bcf6c7a65

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_symm_resolvent_formBound
import Theorems.Thm_TeschlQM_Atomic_spectrum_add_nonneg_mem_spectrum
import Theorems.Thm_TeschlQM_Shared_essentialSpectrum_exists_weyl_sequence
import Theorems.Thm_TeschlQM_Shared_isBoundedBelowBy_of_spectrum_ge
import Theorems.Thm_TeschlQM_Atomic_tendsto_integral_mul_normSq_of_weakly_null
import Theorems.Thm_TeschlQM_Atomic_atomicHamiltonian_localization_lower_bound

/-! Reduction of the essential-spectrum identity (11.9) of HVZ (Teschl Thm 11.2) to six children:
D0 self-adjointness/semiboundedness/kinetic form bound of H^N, D1 σ(H^{N-1})+[0,∞) ⊆ σ(H^N),
D2 Weyl criterion, D3a spectral lower bound ⇒ form lower bound, D3b Rellich compactness,
D3c IMS localization lower bound. -/

set_option autoImplicit false

namespace HVZC3Red
open TeschlQM.Shared TeschlQM.Atomic MeasureTheory Filter Topology
open scoped InnerProductSpace

/-- C3 itself (spec_ess.json). -/
def C3 : Prop :=
  ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ N : ℕ, 1 ≤ N → ∀ lam : ℝ,
    (lam : ℂ) ∈ spectrum (atomicHamiltonian γne γee (N - 1)) →
    (∀ z ∈ spectrum (atomicHamiltonian γne γee (N - 1)), z.im = 0 ∧ lam ≤ z.re) →
    essentialSpectrum (atomicHamiltonian γne γee N) = (fun t : ℝ => (t : ℂ)) '' Set.Ici lam

/-- D0 (Teschl Thm 11.1, p. 241, from the C1/C2 proofs: Kato–Rellich + Hardy): H^N is symmetric,
has a real resolvent point, is bounded below, and its form controls the kinetic form. -/
def D0 : Prop :=
  ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ N : ℕ,
    IsSymmetric (atomicHamiltonian γne γee N) ∧
    (∃ t : ℝ, (t : ℂ) ∈ resolventSet (atomicHamiltonian γne γee N)) ∧
    (∃ γ : ℝ, IsBoundedBelowBy (atomicHamiltonian γne γee N) γ) ∧
    ∃ C : ℝ, ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
      (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈
        (atomicHamiltonian γne γee N).domain),
      (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re ≤
        2 * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          atomicHamiltonian γne γee N ⟨ψ, hψ⟩⟫_ℂ).re +
        C * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2

/-- D1 (⊇, Teschl Thm 11.2 proof p. 243, first half: Weyl sequence ψ^{N-1} ⊗ plane wave moved
to infinity): σ(H^{N-1}) + [0,∞) ⊆ σ(H^N) on the real points. -/
def D1 : Prop :=
  ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ N : ℕ, 1 ≤ N → ∀ μ : ℝ,
    (μ : ℂ) ∈ spectrum (atomicHamiltonian γne γee (N - 1)) → ∀ s : ℝ, 0 ≤ s →
      ((μ + s : ℝ) : ℂ) ∈ spectrum (atomicHamiltonian γne γee N)

/-- D2 (Weyl criterion, Teschl Lemma 6.17, one direction): for a symmetric operator with a real
resolvent point (hence self-adjoint), every point of σ_ess is real and carries a singular Weyl
sequence. -/
def D2 : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H), IsSymmetric A → ∀ t : ℝ, (t : ℂ) ∈ resolventSet A →
    ∀ z ∈ essentialSpectrum A, z.im = 0 ∧
      ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
        (∀ φ : H, Tendsto (fun n => ⟪φ, (ψ n : H)⟫_ℂ) atTop (𝓝 0)) ∧
        Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0)

/-- D3a (inf σ(A) is a form lower bound, Teschl (2.?) / Thm 3.? via spectral theorem; here:
self-adjoint, bounded below, σ ⊆ [lam,∞) ⇒ A ≥ lam). -/
def D3a : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H), IsSymmetric A → ∀ γ : ℝ, IsBoundedBelowBy A γ →
    ∀ t : ℝ, (t : ℂ) ∈ resolventSet A → ∀ lam : ℝ,
    (∀ z ∈ spectrum A, z.im = 0 ∧ lam ≤ z.re) → IsBoundedBelowBy A lam

/-- D3b (local compactness / Rellich, Teschl Lemma 7.? : f(x)(H0+1)^{-1/2} compact for f → 0):
weakly null, H¹-bounded sequences have ∫ W|ψ_n|² → 0 for bounded W vanishing at infinity. -/
def D3b : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : EuclideanSpace ℝ ι → ℝ), Measurable W →
    (∃ C : ℝ, ∀ x, |W x| ≤ C) → (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) →
    ∀ ψ : ℕ → (freeHamiltonian ι).domain,
      (∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
        Tendsto (fun n => ⟪φ, (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))⟫_ℂ)
          atTop (𝓝 0)) →
      (∃ B : ℝ, ∀ n, ‖(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ≤ B ∧
        (⟪(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))),
          freeHamiltonian ι (ψ n)⟫_ℂ).re ≤ B) →
      Tendsto (fun n => ∫ x, W x *
        ‖((ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
          EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) atTop (𝓝 0)

/-- D3c (IMS localization lower bound, Teschl Thm 11.2 proof p. 243, (11.12)-(11.14), with the
Ruelle–Simon partition b43a7360 and Lemma 11.3): H^N ≥ lam - δ - δ H0 - W_δ, W_δ → 0 at ∞. -/
def D3c : Prop :=
  ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ N : ℕ, 1 ≤ N → ∀ lam : ℝ,
    IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam → ∀ δ : ℝ, 0 < δ →
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
        (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈
          (atomicHamiltonian γne γee N).domain),
        (lam - δ) * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2
          - δ * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
              freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re
          - ∫ x, W x * ‖((ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) :
              EuclideanSpace ℝ (Fin N × Fin 3) → ℂ) x‖ ^ 2
          ≤ (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
              atomicHamiltonian γne γee N ⟨ψ, hψ⟩⟫_ℂ).re

lemma dom_free {γne γee : ℝ} {N : ℕ}
    (ψ : (atomicHamiltonian γne γee N).domain) :
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈
      (freeHamiltonian (Fin N × Fin 3)).domain := by
  exact (Submodule.mem_inf.mp (show (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
    ∈ (freeHamiltonian (Fin N × Fin 3)).domain ⊓
      (mulOp volume (fun x => ((atomicPotential γne γee N x : ℝ) : ℂ))).domain from ψ.2)).1

theorem c3_of_children (h0 : D0) (h1 : D1) (h2 : D2) (h3a : D3a) (h3b : D3b) (h3c : D3c) :
    C3 := by
  intro γne γee hne hee N hN lam hlam hmin
  have hsup : ∀ t : ℝ, lam ≤ t → (t : ℂ) ∈ spectrum (atomicHamiltonian γne γee N) := by
    intro t ht
    have := h1 γne γee hne hee N hN lam hlam (t - lam) (by linarith)
    simpa using this
  ext z
  constructor
  · intro hz
    obtain ⟨hS, ⟨t0, ht0⟩, -, C, hC⟩ := h0 γne γee hne hee N
    obtain ⟨hzi, ψ, hn1, hw, hconv⟩ := h2 _ hS t0 ht0 z hz
    obtain ⟨hS', ⟨t1, ht1⟩, ⟨γ', hγ'⟩, -⟩ := h0 γne γee hne hee (N - 1)
    have hform : IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam :=
      h3a _ hS' γ' hγ' t1 ht1 lam hmin
    set a : ℕ → ℝ := fun n => (⟪((ψ n : (atomicHamiltonian γne γee N).domain) :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
        atomicHamiltonian γne γee N (ψ n)⟫_ℂ).re with ha_def
    have ha : Tendsto a atTop (𝓝 z.re) := by
      have hdiff : ∀ n, |a n - z.re| ≤ ‖atomicHamiltonian γne γee N (ψ n) - z •
          ((ψ n : (atomicHamiltonian γne γee N).domain) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ := by
        intro n
        have e1 : a n - z.re = (⟪((ψ n : (atomicHamiltonian γne γee N).domain) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
            atomicHamiltonian γne γee N (ψ n) - z • ((ψ n : (atomicHamiltonian γne γee N).domain) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))⟫_ℂ).re := by
          rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hn1]
          simp [ha_def]
        rw [e1]
        refine (Complex.abs_re_le_norm _).trans ?_
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hn1, one_mul]
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _)
        (fun n => by rw [Real.norm_eq_abs]; exact hdiff n) hconv)
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto a ha)
    have haM : ∀ n, a n ≤ M := fun n =>
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hM _ ⟨n, rfl⟩)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨0, rfl⟩)
    set B : ℝ := 2 * M + |C| + 1 with hB
    have hB1 : 0 < 1 + B := by positivity
    have hq : ∀ n, (⟪((ψ n : (atomicHamiltonian γne γee N).domain) :
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
        freeHamiltonian (Fin N × Fin 3) ⟨_, dom_free (ψ n)⟩⟫_ℂ).re ≤ B := by
      intro n
      have h := hC ⟨_, dom_free (ψ n)⟩ (ψ n).2
      simp only [Subtype.coe_eta, hn1, one_pow, mul_one] at h
      have := haM n
      have : C ≤ |C| := le_abs_self C
      simp only [ha_def] at *
      linarith
    have key : ∀ δ : ℝ, 0 < δ → lam - δ - δ * B ≤ z.re := by
      intro δ hδ
      obtain ⟨W, hWm, hWb, hWt, hW⟩ := h3c γne γee hne hee N hN lam hform δ hδ
      have hI := h3b (Fin N × Fin 3) W hWm hWb hWt (fun n => ⟨_, dom_free (ψ n)⟩)
        (fun φ => hw φ) ⟨B, fun n => ⟨by rw [hn1]; linarith [abs_nonneg C], hq n⟩⟩
      have hl := (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := lam - δ - δ * B)).sub hI
      rw [sub_zero (lam - δ - δ * B)] at hl
      refine le_of_tendsto_of_tendsto' hl ha (fun n => ?_)
      have h := hW ⟨_, dom_free (ψ n)⟩ (ψ n).2
      simp only [Subtype.coe_eta, hn1, one_pow, mul_one] at h
      have := hq n
      have : δ * (⟪((ψ n : (atomicHamiltonian γne γee N).domain) :
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
        freeHamiltonian (Fin N × Fin 3) ⟨_, dom_free (ψ n)⟩⟫_ℂ).re ≤ δ * B :=
        mul_le_mul_of_nonneg_left (hq n) hδ.le
      simp only [ha_def]
      linarith
    refine ⟨z.re, ?_, ?_⟩
    · show lam ≤ z.re
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have k := key (ε / (1 + B)) (by positivity)
      have e : ε / (1 + B) + ε / (1 + B) * B = ε / (1 + B) * (1 + B) := by ring
      rw [div_mul_cancel₀ _ hB1.ne'] at e
      show lam ≤ z.re + ε
      linarith
    · apply Complex.ext <;> simp [hzi]
  · rintro ⟨t, ht, rfl⟩
    have ht' : lam ≤ t := ht
    refine ⟨hsup t ht', ?_⟩
    rintro ⟨-, -, ⟨ε, hε, hiso⟩, -⟩
    have e : ((t + ε / 2 : ℝ) : ℂ) - (t : ℂ) = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
    have hw := hiso ((t + ε / 2 : ℝ) : ℂ) (hsup _ (by linarith)) (by
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith)
    have hw' : ((t + ε / 2 : ℝ) : ℂ) = (t : ℂ) := hw
    have : t + ε / 2 = t := by exact_mod_cast hw'
    linarith

end HVZC3Red

open TeschlQM.Atomic in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ)
    (hN : 1 ≤ N) (lam : ℝ)
    (hlam : (lam : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)))
    (hmin : ∀ z ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)), z.im = 0 ∧ lam ≤ z.re) :
    TeschlQM.Shared.essentialSpectrum (atomicHamiltonian γne γee N) =
      (fun t : ℝ => (t : ℂ)) '' Set.Ici lam := by
  refine HVZC3Red.c3_of_children ?_ ?_ ?_ ?_ ?_ ?_ γne γee hne hee N hN lam hlam hmin
  · intro a b ha hb M
    exact TeschlQM.Atomic.atomicHamiltonian_symm_resolvent_formBound a b ha hb M
  · intro a b ha hb M hM μ hμ s hs
    obtain ⟨hsym, hres, -⟩ := TeschlQM.Atomic.atomicHamiltonian_symm_resolvent_formBound a b ha hb (M - 1)
    exact TeschlQM.Atomic.spectrum_add_nonneg_mem_spectrum a b ha hb M hM hsym hres μ hμ s hs
  · intro H _ _ _ A hA t ht z hz
    exact TeschlQM.Shared.essentialSpectrum_exists_weyl_sequence A hA t ht z hz
  · intro H _ _ _ A hA γ hγ t ht l hl
    exact TeschlQM.Shared.isBoundedBelowBy_of_spectrum_ge A hA γ hγ t ht l hl
  · intro ι _ W hWm hWb hWt ψ hw hb
    exact TeschlQM.Atomic.tendsto_integral_mul_normSq_of_weakly_null ι W hWm hWb hWt ψ hw hb
  · intro a b ha hb M hM l hl δ hδ
    exact TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound a b ha hb M hM l hl δ hδ
