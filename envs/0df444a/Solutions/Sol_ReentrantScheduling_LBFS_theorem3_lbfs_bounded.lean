-- Prove2me | solution 1 for ReentrantScheduling.LBFS.theorem3_lbfs_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:02:25.178285+00:00
-- url     : https://prove2.me/submissions/0a99f2e2-a534-454a-8dd7-8fcbb08c1b7e

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants
import Theorems.Thm_ReentrantScheduling_LBFS_eq10_remaining_delay

set_option autoImplicit false

namespace LBFSThm3Aux

open ReentrantScheduling.LBFS

section
variable {L : Line} (R : Run L)

/-- the set of parts counted by `x t`. -/
def sys (t : ℝ) : Set R.Part := {p | R.α p ≤ t ∧ (t : WithTop ℝ) < R.exit p}

lemma sys_finite (t : ℝ) : (sys R t).Finite :=
  (R.released_finite t).subset (fun _ hp => hp.1)

noncomputable def xn (t : ℝ) : ℕ := (sys R t).ncard

lemma x_eq (t : ℝ) : R.x t = (xn R t : ℕ∞) := by
  rw [xn, (sys_finite R t).cast_ncard_eq]
  rfl

noncomputable def N (t : ℝ) : ℕ := {p | R.α p ≤ t}.ncard

lemma N_mono {s t : ℝ} (h : s ≤ t) : N R s ≤ N R t :=
  Set.ncard_le_ncard (fun _ hp => le_trans hp h) (R.released_finite t)

lemma N_lt {s t : ℝ} (h : s < t) (hrel : ∃ π, R.α π = t) : N R s < N R t := by
  obtain ⟨π, hπ⟩ := hrel
  apply Set.ncard_lt_ncard _ (R.released_finite t)
  refine ⟨fun _ hp => le_trans hp h.le, fun hsub => ?_⟩
  have : R.α π ≤ s := hsub (show R.α π ≤ t from hπ.le)
  linarith
end

lemma w_nonneg (L : Line) (σ : Fin L.S) : 0 ≤ L.w σ := by
  unfold Line.w
  exact Finset.sum_nonneg (fun i _ => div_nonneg (L.τ_pos i).le (Nat.cast_nonneg _))

lemma w_le_wbar (L : Line) (σ : Fin L.S) : L.w σ ≤ L.wbar :=
  Finset.le_sup' L.w (Finset.mem_univ σ)

lemma wbar_nonneg (L : Line) : 0 ≤ L.wbar :=
  (w_nonneg L _).trans (w_le_wbar L (L.center L.first))

lemma wk_le_wbar (L : Line) (k : Fin L.l) : L.wk k ≤ L.wbar := by
  unfold Line.wk
  apply Finset.sup'_le
  intro j _
  refine le_trans ?_ (w_le_wbar L (L.center j))
  unfold Line.w
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2
  · intro i _ _
    exact div_nonneg (L.τ_pos i).le (Nat.cast_nonneg _)

lemma τbar_nonneg (L : Line) : 0 ≤ L.τbar :=
  (L.τ_pos L.first).le.trans (Finset.le_sup' L.τ (Finset.mem_univ _))

lemma cAux_nonneg (L : Line) : ∀ (d : ℕ) (ε : ℝ), 0 ≤ L.cAux d ε
  | 0, ε => by
      rw [Line.cAux]
      exact add_nonneg (τbar_nonneg L) (L.τ_pos _).le
  | d + 1, ε => by
      rw [Line.cAux]
      have h1 := cAux_nonneg L d ε
      have h2 : 0 ≤ 2 * (L.l : ℝ) * L.τbar := by
        have := τbar_nonneg L; positivity
      exact add_nonneg h1 (le_trans h2 (le_max_left _ _))

lemma cLBFS_nonneg (L : Line) (ε : ℝ) : 0 ≤ L.cLBFS ε := cAux_nonneg L _ ε

section
variable {L : Line} (R : Run L)

lemma inBlock_of_sys {π : R.Part} {t : ℝ} (h : π ∈ sys R t) (k : Fin L.l) (hk : k.val = 0) :
    R.inBlock π k t := by
  classical
  obtain ⟨hα, hex⟩ := h
  let s : Finset (Fin L.l) :=
    Finset.univ.filter (fun i => R.entry π ≤ i ∧ R.arrive π i ≤ (t : WithTop ℝ))
  have hent : R.entry π ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
    simp only [Run.arrive]
    exact WithTop.coe_le_coe.mpr hα
  have hi : s.max' ⟨_, hent⟩ ∈ s := Finset.max'_mem _ _
  set i := s.max' ⟨_, hent⟩ with hi_def
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  refine ⟨i, ?_, hi.1, hi.2, ?_⟩
  · rw [Fin.le_def, hk]; exact Nat.zero_le _
  · by_cases h : i.val + 1 < L.l
    · let j : Fin L.l := ⟨i.val + 1, h⟩
      have hij : i < j := by rw [Fin.lt_def]; simp [j]
      have hej : R.entry π < j := lt_of_le_of_lt hi.1 hij
      have hj : j ∉ s := by
        intro hjs
        have := Finset.le_max' s j hjs
        exact absurd this (not_le.mpr hij)
      have harr : R.arrive π j = R.start π i + ((L.τ i : ℝ) : WithTop ℝ) := by
        unfold Run.arrive
        rw [if_neg (ne_of_gt hej), dif_pos hej]
        have e : (⟨j.val - 1, by omega⟩ : Fin L.l) = i := Fin.ext (by simp [j])
        rw [e]
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hj
      have := hj hej.le
      rw [harr] at this
      exact this
    · have hil : i = L.last := Fin.ext (by have := i.isLt; simp [Line.last]; omega)
      rw [hil]
      exact hex

variable {lam γ : ℝ}

lemma arr_count (hA : R.Arrivals lam γ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    (({p | ¬ R.initial p ∧ s < R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) ≤
      lam * (t - s) + γ := by
  have hfin : ({p | ¬ R.initial p ∧ s < R.α p ∧ R.α p ≤ t} : Set R.Part).Finite :=
    (R.released_finite t).subset (fun _ hp => hp.2.2)
  have h := hA s t hs hst
  rw [← hfin.cast_ncard_eq] at h
  have hr : 0 ≤ lam * (t - s) + γ := by nlinarith
  rw [← ENNReal.ofReal_le_ofReal_iff hr, ENNReal.ofReal_natCast]
  simpa using h

lemma arr_count_closed (hA : R.Arrivals lam γ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (({p | ¬ R.initial p ∧ s ≤ R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) ≤
      lam * (t - s) + γ := by
  apply le_of_forall_pos_le_add
  intro e he
  set δ := min s (e / (lam + 1)) with hδdef
  have hδ : 0 < δ := lt_min hs (div_pos he (by linarith))
  have hδs : δ ≤ s := min_le_left _ _
  have hδe : lam * δ ≤ e := by
    have h1 : δ ≤ e / (lam + 1) := min_le_right _ _
    have h2 : lam * δ ≤ lam * (e / (lam + 1)) := mul_le_mul_of_nonneg_left h1 hlam
    have h3 : lam * (e / (lam + 1)) ≤ e := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsub : ({p | ¬ R.initial p ∧ s ≤ R.α p ∧ R.α p ≤ t} : Set R.Part) ⊆
      {p | ¬ R.initial p ∧ (s - δ) < R.α p ∧ R.α p ≤ t} :=
    fun _ hp => ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  have hfin : ({p | ¬ R.initial p ∧ (s - δ) < R.α p ∧ R.α p ≤ t} : Set R.Part).Finite :=
    (R.released_finite t).subset (fun _ hp => hp.2.2)
  have h1 : (({p | ¬ R.initial p ∧ s ≤ R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) ≤
      (({p | ¬ R.initial p ∧ (s - δ) < R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have h2 := arr_count R hA hlam hγ (s := s - δ) (t := t) (by linarith) (by linarith)
  have : lam * (t - (s - δ)) + γ = lam * (t - s) + γ + lam * δ := by ring
  linarith

/-- The hypothesis supplied by `eq10_remaining_delay` at `k = 0`. -/
def Eq10At0 (L : Line) (R : Run L) (ε : ℝ) : Prop :=
  ∀ (π : R.Part) (t₀ : ℝ), 0 ≤ t₀ → R.inBlock π ⟨0, L.l_pos⟩ t₀ → ∀ x : ℕ,
    (R.ahead π t₀).encard = x →
      R.exit π ≤ ((t₀ + L.c ⟨0, L.l_pos⟩ ε + (L.wk ⟨0, L.l_pos⟩ + ε) * x : ℝ) : WithTop ℝ)

lemma delay {ε : ℝ} (hε : 0 < ε) (h10 : Eq10At0 L R ε) {π : R.Part} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hπ : π ∈ sys R t₀) :
    R.exit π ≤ ((t₀ + L.cLBFS ε + (L.wbar + ε) * xn R t₀ : ℝ) : WithTop ℝ) := by
  have hsub : R.ahead π t₀ ⊆ sys R t₀ := fun _ hq => hq.1
  have hfin : (R.ahead π t₀).Finite := (sys_finite R t₀).subset hsub
  have h := h10 π t₀ ht₀ (inBlock_of_sys R hπ _ rfl) (R.ahead π t₀).ncard
    hfin.cast_ncard_eq.symm
  have hc : L.c ⟨0, L.l_pos⟩ ε = L.cLBFS ε := by simp [Line.c, Line.cLBFS]
  rw [hc] at h
  refine h.trans (WithTop.coe_le_coe.mpr ?_)
  have ha : ((R.ahead π t₀).ncard : ℝ) ≤ (xn R t₀ : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (sys_finite R t₀)
  have hw := wk_le_wbar L ⟨0, L.l_pos⟩
  have hW : 0 ≤ L.wbar + ε := by have := wbar_nonneg L; linarith
  have h0 : (0 : ℝ) ≤ (R.ahead π t₀).ncard := Nat.cast_nonneg _
  have e1 : (L.wk ⟨0, L.l_pos⟩ + ε) * (R.ahead π t₀).ncard ≤
      (L.wbar + ε) * (R.ahead π t₀).ncard := mul_le_mul_of_nonneg_right (by linarith) h0
  have e2 : (L.wbar + ε) * (R.ahead π t₀).ncard ≤ (L.wbar + ε) * xn R t₀ :=
    mul_le_mul_of_nonneg_left ha hW
  linarith

lemma one_step (hR : R.Admissible L.lbfsPrio) (hA : R.Arrivals lam γ) (hlam : 0 ≤ lam)
    (hγ : 0 ≤ γ) {ε : ℝ} (hε : 0 < ε) (h10 : Eq10At0 L R ε) (t : ℝ) (ht : 0 ≤ t) :
    xn R t = 0 ∨
    ((xn R t : ℝ) ≤ (1 + lam * (L.wbar + ε)) * xn R 0 + (lam * L.cLBFS ε + γ) ∧
       t ≤ L.cLBFS ε + (L.wbar + ε) * xn R 0) ∨
    ∃ s : ℝ, 0 < s ∧ s ≤ t ∧ (∃ π, R.α π = s) ∧
      t - s ≤ L.cLBFS ε + (L.wbar + ε) * xn R s ∧
      (xn R t : ℝ) ≤ (lam * L.cLBFS ε + γ) + lam * (L.wbar + ε) * xn R s := by
  classical
  by_cases h0 : xn R t = 0
  · exact Or.inl h0
  right
  have hne : (sys R t).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    exact h0 (by simp [xn, hcon])
  obtain ⟨π, hπmem, hπmin⟩ :=
    (sys_finite R t).toFinset.exists_min_image R.ord (by simpa using hne)
  rw [Set.Finite.mem_toFinset] at hπmem
  have hmin : ∀ q ∈ sys R t, R.ord π ≤ R.ord q :=
    fun q hq => hπmin q ((Set.Finite.mem_toFinset _).mpr hq)
  have hαnn : 0 ≤ R.α π := by
    by_cases hi : R.initial π
    · rw [R.initial_zero π hi]
    · exact R.released_nonneg π hi
  have hπs : π ∈ sys R (R.α π) :=
    ⟨le_refl _, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hπmem.1) hπmem.2⟩
  have hD := delay R hε h10 hαnn hπs
  have htlt : t < R.α π + L.cLBFS ε + (L.wbar + ε) * xn R (R.α π) :=
    WithTop.coe_lt_coe.mp (lt_of_lt_of_le hπmem.2 hD)
  rcases eq_or_lt_of_le hαnn with hα0 | hαpos
  · left
    rw [← hα0] at htlt
    refine ⟨?_, by linarith⟩
    have hsub : sys R t ⊆ sys R 0 ∪ {p | ¬ R.initial p ∧ 0 < R.α p ∧ R.α p ≤ t} := by
      intro q hq
      by_cases hq0 : R.α q ≤ 0
      · left
        exact ⟨hq0, lt_of_le_of_lt (WithTop.coe_le_coe.mpr ht) hq.2⟩
      · right
        push Not at hq0
        refine ⟨fun hi => ?_, hq0, hq.1⟩
        rw [R.initial_zero q hi] at hq0
        exact lt_irrefl _ hq0
    have hfin2 : ({p | ¬ R.initial p ∧ 0 < R.α p ∧ R.α p ≤ t} : Set R.Part).Finite :=
      (R.released_finite t).subset (fun _ hp => hp.2.2)
    have h1 : xn R t ≤ xn R 0 + ({p | ¬ R.initial p ∧ 0 < R.α p ∧ R.α p ≤ t} : Set R.Part).ncard :=
      (Set.ncard_le_ncard hsub ((sys_finite R 0).union hfin2)).trans (Set.ncard_union_le _ _)
    have h1' : (xn R t : ℝ) ≤ xn R 0 +
        (({p | ¬ R.initial p ∧ 0 < R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) := by
      exact_mod_cast h1
    have h2 := arr_count R hA hlam hγ (le_refl (0:ℝ)) ht
    have h3 : lam * t ≤ lam * (0 + L.cLBFS ε + (L.wbar + ε) * xn R 0) :=
      mul_le_mul_of_nonneg_left htlt.le hlam
    nlinarith
  · right
    have hπi : ¬ R.initial π := by
      intro hi
      rw [R.initial_zero π hi] at hαpos
      exact lt_irrefl _ hαpos
    refine ⟨R.α π, hαpos, hπmem.1, ⟨π, rfl⟩, by linarith, ?_⟩
    have hsub : sys R t ⊆ {p | ¬ R.initial p ∧ R.α π ≤ R.α p ∧ R.α p ≤ t} := by
      intro q hq
      have hqi : ¬ R.initial q := by
        intro hi
        have := hR.ord_initial q π hi hπi
        have := hmin q hq
        omega
      refine ⟨hqi, ?_, hq.1⟩
      by_contra hlt
      push Not at hlt
      have := hR.ord_release q π hqi hπi hlt
      have := hmin q hq
      omega
    have hfin2 : ({p | ¬ R.initial p ∧ R.α π ≤ R.α p ∧ R.α p ≤ t} : Set R.Part).Finite :=
      (R.released_finite t).subset (fun _ hp => hp.2.2)
    have h1 : (xn R t : ℝ) ≤
        (({p | ¬ R.initial p ∧ R.α π ≤ R.α p ∧ R.α p ≤ t} : Set R.Part).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin2
    have h2 := arr_count_closed R hA hlam hγ hαpos hπmem.1
    have h3 : lam * (t - R.α π) ≤ lam * (L.cLBFS ε + (L.wbar + ε) * xn R (R.α π)) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam
    nlinarith

end

section
variable {L : Line} (R : Run L) {lam γ : ℝ}

lemma bounded (hR : R.Admissible L.lbfsPrio) (hA : R.Arrivals lam γ) (hlam : 0 ≤ lam)
    (hγ : 0 ≤ γ) {ε : ℝ} (hε : 0 < ε) (h10 : Eq10At0 L R ε)
    (hgap : lam * (L.wbar + ε) < 1) (t : ℝ) (ht : 0 ≤ t) :
    (xn R t : ℝ) ≤ max ((1 + lam * (L.wbar + ε)) * xn R 0 + (lam * L.cLBFS ε + γ))
      (2 * (lam * L.cLBFS ε + γ) / (1 - lam * (L.wbar + ε))) := by
  set ρ := lam * (L.wbar + ε) with hρ
  set K := lam * L.cLBFS ε + γ with hKdef
  set M := max ((1 + ρ) * xn R 0 + K) (2 * K / (1 - ρ)) with hMdef
  have hK : 0 ≤ K := by have := cLBFS_nonneg L ε; positivity
  have hρ0 : 0 ≤ ρ := by have := wbar_nonneg L; positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  have hKM : K / (1 - ρ) ≤ M := by
    refine le_trans ?_ (le_max_right _ _)
    rw [div_le_div_iff_of_pos_right h1ρ]; linarith
  have hKM' : K ≤ (1 - ρ) * M := by
    rw [div_le_iff₀ h1ρ] at hKM; linarith
  have hM0 : 0 ≤ M := le_trans (div_nonneg hK h1ρ.le) hKM
  have hmono : ∀ y : ℝ, y ≤ M → K + ρ * y ≤ M := by
    intro y hy; nlinarith [mul_le_mul_of_nonneg_left hy hρ0]
  have hself : ∀ y : ℝ, y ≤ K + ρ * y → y ≤ M := by
    intro y hy
    have h2 : y * (1 - ρ) ≤ K := by nlinarith
    have h3 : y ≤ K / (1 - ρ) := by rw [le_div_iff₀ h1ρ]; exact h2
    linarith
  have hAM : (1 + ρ) * xn R 0 + K ≤ M := le_max_left _ _
  have rel : ∀ s : ℝ, 0 < s → (∃ π, R.α π = s) →
      (∀ u : ℝ, 0 ≤ u → N R u < N R s → (xn R u : ℝ) ≤ M) → (xn R s : ℝ) ≤ M := by
    intro s hs hrel IH
    rcases one_step R hR hA hlam hγ hε h10 s hs.le with h | ⟨h, -⟩ | ⟨s2, hs2, hs2s, -, -, hb⟩
    · rw [h]; simpa using hM0
    · exact h.trans hAM
    · rcases eq_or_lt_of_le hs2s with heq | hlt
      · subst heq; exact hself _ hb
      · exact hb.trans (hmono _ (IH s2 hs2.le (N_lt R hlt hrel)))
  suffices H : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → N R t = n → (xn R t : ℝ) ≤ M from H _ t ht rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro t ht hn
    rcases one_step R hR hA hlam hγ hε h10 t ht with h | ⟨h, -⟩ | ⟨s, hs, hst, hrel, -, hb⟩
    · rw [h]; simpa using hM0
    · exact h.trans hAM
    · have hsM : (xn R s : ℝ) ≤ M := rel s hs hrel (fun u hu hlt =>
        IH (N R u) (lt_of_lt_of_le hlt ((N_mono R hst).trans hn.le)) u hu rfl)
      exact hb.trans (hmono _ hsM)

lemma eventually_le (hR : R.Admissible L.lbfsPrio) (hA : R.Arrivals lam γ) (hlam : 0 ≤ lam)
    (hγ : 0 ≤ γ) {ε : ℝ} (hε : 0 < ε) (h10 : Eq10At0 L R ε)
    (hgap : lam * (L.wbar + ε) < 1) {M : ℝ} (hbd : ∀ t : ℝ, 0 ≤ t → (xn R t : ℝ) ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (xn R t : ℝ) ≤ (lam * L.cLBFS ε + γ) / (1 - lam * (L.wbar + ε)) + δ := by
  have hc0 : 0 ≤ L.cLBFS ε := cLBFS_nonneg L ε
  have hW0 : 0 ≤ L.wbar + ε := by have := wbar_nonneg L; linarith
  set ρ := lam * (L.wbar + ε) with hρ
  set K := lam * L.cLBFS ε + γ with hKdef
  set c := L.cLBFS ε with hc
  set W := L.wbar + ε with hW
  have hK : 0 ≤ K := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg _) (hbd 0 le_rfl)
  set D := c + W * M + 1 with hD
  have hWM : 0 ≤ W * M := mul_nonneg hW0 hM0
  have hD0 : 0 < D := by linarith
  have hKρ : 0 ≤ K / (1 - ρ) := div_nonneg hK h1ρ.le
  have hfix : K + ρ * (K / (1 - ρ)) = K / (1 - ρ) := by
    field_simp
    ring
  have claim : ∀ j : ℕ, ∀ t : ℝ, ((j : ℝ) + 1) * D ≤ t →
      (xn R t : ℝ) ≤ K / (1 - ρ) + ρ ^ j * M := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have ht0 : 0 ≤ t := by simp at ht; linarith
      simp only [pow_zero, one_mul]
      linarith [hbd t ht0]
    | succ j ih =>
      intro t ht
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      push_cast at ht
      have hjD : 0 ≤ (j : ℝ) * D := mul_nonneg hj0 hD0.le
      have ht0 : 0 ≤ t := by nlinarith
      rcases one_step R hR hA hlam hγ hε h10 t ht0 with h | ⟨-, h⟩ | ⟨s, hs, hst, -, hts, hb⟩
      · rw [h]; simp only [Nat.cast_zero]; positivity
      · exfalso
        have h1 := hbd 0 le_rfl
        have : W * xn R 0 ≤ W * M := mul_le_mul_of_nonneg_left h1 hW0
        nlinarith
      · have hsM := hbd s hs.le
        have h4 : W * xn R s ≤ W * M := mul_le_mul_of_nonneg_left hsM hW0
        have hsT : ((j : ℝ) + 1) * D ≤ s := by nlinarith
        have h5 := ih s hsT
        calc (xn R t : ℝ) ≤ K + ρ * xn R s := hb
          _ ≤ K + ρ * (K / (1 - ρ) + ρ ^ j * M) := by
              nlinarith [mul_le_mul_of_nonneg_left h5 hρ0]
          _ = (K + ρ * (K / (1 - ρ))) + ρ ^ (j + 1) * M := by ring
          _ = K / (1 - ρ) + ρ ^ (j + 1) * M := by rw [hfix]
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (M + 1) by positivity) hgap
  refine ⟨((j : ℝ) + 1) * D, fun t ht => ?_⟩
  have h := claim j t ht
  have hpow0 : 0 ≤ ρ ^ j := pow_nonneg hρ0 j
  have h6 : ρ ^ j * (M + 1) < δ := by rwa [lt_div_iff₀ (by linarith)] at hj
  have h7 : ρ ^ j * M ≤ δ := by nlinarith
  linarith

theorem theorem3_of_eq10 (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ)
    (_hload : L.load lam < 1) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (hA : R.Arrivals lam γ) (ε : ℝ) (hε : 0 < ε) (hgap : 0 < 1 - L.load lam - lam * ε)
    (h10 : Eq10At0 L R ε) :
    (∀ t : ℝ, 0 ≤ t → ((R.x t : ℕ∞) : ENNReal) ≤
        max (ENNReal.ofReal (1 + L.load lam + lam * ε) * ((R.x 0 : ℕ∞) : ENNReal) +
              ENNReal.ofReal (lam * L.cLBFS ε + γ))
          (ENNReal.ofReal (2 * (lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)))) ∧
    Filter.limsup (fun t : ℝ => ((R.x t : ℕ∞) : ENNReal)) Filter.atTop ≤
      ENNReal.ofReal ((lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)) := by
  have hρe : L.load lam + lam * ε = lam * (L.wbar + ε) := by unfold Line.load; ring
  have hgap' : lam * (L.wbar + ε) < 1 := by linarith
  have h1 : 1 - L.load lam - lam * ε = 1 - lam * (L.wbar + ε) := by linarith
  have h2 : 1 + L.load lam + lam * ε = 1 + lam * (L.wbar + ε) := by linarith
  rw [h1, h2]
  have hK : 0 ≤ lam * L.cLBFS ε + γ := by have := cLBFS_nonneg L ε; positivity
  have hρ0 : 0 ≤ lam * (L.wbar + ε) := by
    have := wbar_nonneg L; have : 0 ≤ L.wbar + ε := by linarith
    positivity
  have hcast : ∀ t, ((R.x t : ℕ∞) : ENNReal) = ENNReal.ofReal (xn R t : ℝ) := by
    intro t; rw [x_eq, ENNReal.ofReal_natCast]; simp
  have hbd := bounded R hR hA hlam hγ hε h10 hgap'
  constructor
  · intro t ht
    rw [hcast, hcast, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by positivity) hK, ← ENNReal.ofReal_max]
    exact ENNReal.ofReal_le_ofReal (hbd t ht)
  · apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    obtain ⟨T, hT⟩ := eventually_le R hR hA hlam hγ hε h10 hgap' hbd
      (show (0 : ℝ) < δ from hδ)
    refine Filter.limsup_le_of_le (h := ?_)
    rw [Filter.eventually_atTop]
    refine ⟨T, fun t ht => ?_⟩
    have hq : 0 ≤ (lam * L.cLBFS ε + γ) / (1 - lam * (L.wbar + ε)) :=
      div_nonneg hK (by linarith)
    rw [hcast, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hq (NNReal.coe_nonneg δ)]
    exact ENNReal.ofReal_le_ofReal (hT t ht)

end

end LBFSThm3Aux

open ReentrantScheduling.LBFS in
theorem solution (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ)
    (hload : L.load lam < 1) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (hA : R.Arrivals lam γ) (ε : ℝ) (hε : 0 < ε) (hgap : 0 < 1 - L.load lam - lam * ε) :
    (∀ t : ℝ, 0 ≤ t → ((R.x t : ℕ∞) : ENNReal) ≤
        max (ENNReal.ofReal (1 + L.load lam + lam * ε) * ((R.x 0 : ℕ∞) : ENNReal) +
              ENNReal.ofReal (lam * L.cLBFS ε + γ))
          (ENNReal.ofReal (2 * (lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)))) ∧
    Filter.limsup (fun t : ℝ => ((R.x t : ℕ∞) : ENNReal)) Filter.atTop ≤
      ENNReal.ofReal ((lam * L.cLBFS ε + γ) / (1 - L.load lam - lam * ε)) := by
  exact LBFSThm3Aux.theorem3_of_eq10 L lam γ hlam hγ hload R hR hA ε hε hgap
    (fun π t₀ ht₀ hπ x hx =>
      eq10_remaining_delay L R hR ⟨0, L.l_pos⟩ ε hε π t₀ ht₀ hπ x hx)
