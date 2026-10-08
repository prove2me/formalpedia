-- Prove2me | solution 1 for ProcessingNetworks.FluidStability.fluid_limit_compactness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:18:24.367139+00:00
-- url     : https://prove2.me/submissions/95409786-d119-49c2-9588-70a88dcbb40b

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily



namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability Topology

section FLC
variable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ}

lemma flc_T_lip (fam : SPNProcessFamily Mrep sd dat E v φ) (x : Xstate) (ω : Ω) (j : Fin J)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ fam.T x t ω j - fam.T x s ω j ∧
      fam.T x t ω j - fam.T x s ω j ≤ (∑ k, sd.b k) * (t - s) := by
  have hR := fam.relations x
  have hmono : fam.T x s ω j ≤ fam.T x t ω j := hR.T_mono ω j hst
  refine ⟨by linarith, ?_⟩
  rcases eq_or_lt_of_le hst with h | h
  · subst h; simp
  obtain ⟨k, hk⟩ := sd.A_col_nonzero j
  have hcap := hR.T_capacity ω s t k hs h
  have hterm : sd.A k j * (fam.T x t ω j - fam.T x s ω j) ≤
      ∑ j', sd.A k j' * (fam.T x t ω j' - fam.T x s ω j') := by
    apply Finset.single_le_sum (f := fun j' => sd.A k j' * (fam.T x t ω j' - fam.T x s ω j'))
      (fun j' _ => ?_) (Finset.mem_univ j)
    have : 0 ≤ sd.A k j' := by rcases sd.A_binary k j' with h | h <;> rw [h] <;> norm_num
    exact mul_nonneg this (by linarith [hR.T_mono ω j' hst])
  rw [hk, one_mul] at hterm
  have hb : sd.b k ≤ ∑ k, sd.b k :=
    Finset.single_le_sum (f := sd.b) (fun k _ => (sd.b_pos k).le) (Finset.mem_univ k)
  have : 0 ≤ t - s := by linarith
  nlinarith

lemma flc_T_abs (fam : SPNProcessFamily Mrep sd dat E v φ) (x : Xstate) (ω : Ω) (j : Fin J)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |fam.T x a ω j - fam.T x b ω j| ≤ (∑ k, sd.b k) * |a - b| := by
  rcases le_total a b with h | h
  · obtain ⟨h1, h2⟩ := flc_T_lip fam x ω j a b ha h
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h2
  · obtain ⟨h1, h2⟩ := flc_T_lip fam x ω j b a hb h
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
    exact h2

end FLC

/-- functions with `f 0 = 0` and Lipschitz constant `L`. -/
def flcP {J : ℕ} (L : ℝ) : Set (ℝ → Fin J → ℝ) :=
  {f | f 0 = 0 ∧ ∀ t u, dist (f t) (f u) ≤ L * dist t u}

lemma flcP_cont {J : ℕ} {L : ℝ} (hL : 0 ≤ L) {f : ℝ → Fin J → ℝ} (hf : f ∈ flcP L) :
    Continuous f := by
  have : LipschitzWith (Real.toNNReal L) f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.coe_toNNReal L hL]
    exact hf.2 a b
  exact this.continuous

lemma flcP_compact {J : ℕ} {L : ℝ} (hL : 0 ≤ L) : IsCompact (flcP (J := J) L) := by
  have hcl : IsClosed (flcP (J := J) L) := by
    have he : flcP (J := J) L = {f | f 0 = 0} ∩
        ⋂ t : ℝ, ⋂ u : ℝ, {f : ℝ → Fin J → ℝ | dist (f t) (f u) ≤ L * dist t u} := by
      ext f; simp [flcP]
    rw [he]
    apply IsClosed.inter
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · exact isClosed_iInter fun t => isClosed_iInter fun u =>
        isClosed_le ((continuous_apply t).dist (continuous_apply u)) continuous_const
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun t : ℝ => isCompact_closedBall (0 : Fin J → ℝ) (L * |t|))) hcl
  intro f hf
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, forall_const]
  intro t
  have := hf.2 t 0
  rw [hf.1, Real.dist_eq, sub_zero] at this
  exact this

def flcS {J : ℕ} (L : ℝ) : Set C(ℝ, Fin J → ℝ) := {g | (⇑g) ∈ flcP L}

lemma flcS_compact {J : ℕ} {L : ℝ} (hL : 0 ≤ L) : IsCompact (flcS (J := J) L) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have : ContinuousMap.toFun '' (flcS (J := J) L) = flcP L := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        exact ⟨⟨f, flcP_cont hL hf⟩, hf, rfl⟩
    rw [this]
    exact flcP_compact hL
  · intro x0
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε / (L + 1), by positivity, fun x hx g => ?_⟩
    have h1 := g.2.2 x0 x
    rw [dist_comm x0 x] at h1
    calc dist ((g : C(ℝ, Fin J → ℝ)) x0) ((g : C(ℝ, Fin J → ℝ)) x) ≤ L * dist x x0 := h1
      _ ≤ L * (ε / (L + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith)]
        nlinarith

theorem fluid_limit_compactness_core
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω) (C : Set Xstate)
    (hC : ¬ BddAbove ((spnSize Mrep) '' C)) :
    ∃ (x : ℕ → Xstate) (Th : ℝ → Fin J → ℝ) (Zh0 : Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Th ∧ (∀ i, 0 ≤ Zh0 i) ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      Tendsto (fun n i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) 0 ω i : ℝ)) atTop (nhds Zh0) := by
  set L : ℝ := ∑ k, sd.b k with hLdef
  have hL : 0 ≤ L := Finset.sum_nonneg (fun k _ => (sd.b_pos k).le)
  rw [not_bddAbove_iff] at hC
  have hx : ∀ n : ℕ, ∃ y ∈ C, (n : ℝ) + 1 < spnSize Mrep y := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := hC ((n : ℝ) + 1)
    exact ⟨y, hy, h⟩
  choose x hxC hxs using hx
  have hcpos : ∀ n, 0 < spnSize Mrep (x n) := fun n => by
    have := hxs n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  -- scaled functions
  let gf : ℕ → ℝ → Fin J → ℝ := fun n t j =>
    (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * max t 0) ω j
  have hgP : ∀ n, gf n ∈ flcP L := by
    intro n
    have hc := hcpos n
    refine ⟨?_, ?_⟩
    · funext j
      simp only [gf, max_self, mul_zero, Pi.zero_apply]
      rw [(fam.relations (x n)).T_init ω]
      simp
    · intro t u
      rw [dist_pi_le_iff (by positivity)]
      intro j
      simp only [gf, Real.dist_eq]
      rw [← mul_sub, abs_mul, abs_inv, abs_of_pos hc]
      have h1 := flc_T_abs fam (x n) ω j (spnSize Mrep (x n) * max t 0)
        (spnSize Mrep (x n) * max u 0) (by positivity) (by positivity)
      rw [← mul_sub, abs_mul, abs_of_pos hc] at h1
      have h2 : |max t 0 - max u 0| ≤ |t - u| := abs_max_sub_max_le_abs t u 0
      calc (spnSize Mrep (x n))⁻¹ *
            |fam.T (x n) (spnSize Mrep (x n) * max t 0) ω j -
              fam.T (x n) (spnSize Mrep (x n) * max u 0) ω j|
          ≤ (spnSize Mrep (x n))⁻¹ * (L * (spnSize Mrep (x n) * |max t 0 - max u 0|)) := by
            gcongr
        _ = L * |max t 0 - max u 0| := by field_simp
        _ ≤ L * |t - u| := by gcongr
  let g : ℕ → C(ℝ, Fin J → ℝ) := fun n => ⟨gf n, flcP_cont hL (hgP n)⟩
  let zz : ℕ → Fin I → ℝ := fun n i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) 0 ω i : ℝ)
  let Q : Set (Fin I → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)
  have hQ : IsCompact Q := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hzz : ∀ n, zz n ∈ Q := by
    intro n
    simp only [Q, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    have hc := hcpos n
    have hZ : fam.Zx (x n) 0 ω = (Mrep.f (x n)).2 := (fam.relations (x n)).Z_init ω
    simp only [zz, hZ]
    have hle : ((Mrep.f (x n)).2 i : ℝ) ≤ spnSize Mrep (x n) := by
      unfold spnSize
      exact Finset.single_le_sum (f := fun i => ((Mrep.f (x n)).2 i : ℝ))
        (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    refine ⟨by positivity, ?_⟩
    rw [inv_mul_le_iff₀ hc]
    linarith
  have hmem : ∀ n, (g n, zz n) ∈ (flcS (J := J) L) ×ˢ Q := fun n => ⟨hgP n, hzz n⟩
  obtain ⟨⟨G, z0⟩, ⟨_, hz0⟩, ψ, hψ, hlim⟩ :=
    ((flcS_compact (J := J) hL).prod hQ).tendsto_subseq hmem
  refine ⟨x ∘ ψ, ⇑G, z0, fun n => hxC _, ?_, G.continuous, ?_, ?_, ?_⟩
  · apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
    · intro n
      have := hxs (ψ n)
      have : (n : ℝ) ≤ ψ n := by exact_mod_cast hψ.id_le n
      simp only [Function.comp]
      linarith
    · exact tendsto_natCast_atTop_atTop
  · intro i
    have := hz0 i (Set.mem_univ i)
    exact this.1
  · have hG : Tendsto (fun n => g (ψ n)) atTop (𝓝 G) :=
      ((continuous_fst.tendsto _).comp hlim)
    intro T hT ε hε
    have hU := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hG
      (Set.Icc 0 T) isCompact_Icc
    rw [Metric.tendstoUniformlyOn_iff] at hU
    obtain ⟨Nb, hNb⟩ := eventually_atTop.mp (hU ε hε)
    refine ⟨Nb, fun n hn t ht j => ?_⟩
    have h1 := hNb n hn t ht
    have h2 := dist_le_pi_dist ((G : ℝ → Fin J → ℝ) t) ((g (ψ n) : ℝ → Fin J → ℝ) t) j
    rw [Real.dist_eq] at h2
    have h3 : (g (ψ n) : ℝ → Fin J → ℝ) t j =
        (spnSize Mrep (x (ψ n)))⁻¹ * fam.T (x (ψ n)) (spnSize Mrep (x (ψ n)) * t) ω j := by
      show gf (ψ n) t j = _
      simp only [gf, max_eq_left ht.1]
    rw [h3, abs_sub_comm] at h2
    simp only [Function.comp]
    linarith
  · have := ((continuous_snd.tendsto _).comp hlim)
    exact this

end ProcessingNetworks.FluidStability

open ProcessingNetworks.FluidStability
open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability ProcessingNetworks.FluidStability

theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω) (C : Set Xstate)
    (hC : ¬ BddAbove ((spnSize Mrep) '' C)) :
    ∃ (x : ℕ → Xstate) (Th : ℝ → Fin J → ℝ) (Zh0 : Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Th ∧ (∀ i, 0 ≤ Zh0 i) ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      Tendsto (fun n i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) 0 ω i : ℝ)) atTop (nhds Zh0) := by
  exact fluid_limit_compactness_core fam ω C hC
