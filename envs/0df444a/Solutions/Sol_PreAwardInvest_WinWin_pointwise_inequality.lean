-- Prove2me | solution 1 for PreAwardInvest.WinWin.pointwise_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:47:55.950887+00:00
-- url     : https://prove2.me/submissions/288883d8-e3a1-448f-83e8-31e561f6846e

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

open PreAwardInvest.WinWin
open MeasureTheory

namespace PAWpw

variable {N : ℕ}

theorem argminIn_spec [NeZero N] (s : Finset (Fin N)) (hs : s.Nonempty) (key : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    argminIn s key σ ∈ s ∧ ∀ j ∈ s, LexLE key σ (argminIn s key σ) j := by
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun j => toLex (key j, σ j)) hs
  have hex : ∃ i, i ∈ s ∧ ∀ j ∈ s, LexLE key σ i j := by
    refine ⟨i, hi, fun j hj => ?_⟩
    have := hmin j hj
    rw [Prod.Lex.toLex_le_toLex] at this
    exact this
  exact Classical.epsilon_spec hex

theorem argminIn_eq [NeZero N] (s : Finset (Fin N)) (key : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (hi : i ∈ s) (h : ∀ j ∈ s, LexLE key σ i j) :
    argminIn s key σ = i := by
  obtain ⟨hm, hmin⟩ := argminIn_spec s ⟨i, hi⟩ key σ
  have h1 := hmin i hi
  have h2 := h _ hm
  unfold LexLE at h1 h2
  apply σ.injective
  rcases h1 with h1 | ⟨h1e, h1⟩ <;> rcases h2 with h2 | ⟨h2e, h2⟩
  · linarith
  · linarith
  · linarith
  · exact le_antisymm h1 h2

theorem argminIn_univ_eq_iff [NeZero N] (key : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    argminIn Finset.univ key σ = i ↔ ∀ j, LexLE key σ i j := by
  constructor
  · intro h j
    have := (argminIn_spec Finset.univ Finset.univ_nonempty key σ).2 j (Finset.mem_univ j)
    rw [h] at this; exact this
  · intro h
    exact argminIn_eq _ _ _ _ (Finset.mem_univ _) (fun j _ => h j)

theorem measurableSet_argmin [NeZero N] (key : (Fin N → ℝ) → Fin N → ℝ)
    (hk : ∀ j, Measurable fun cv => key cv j) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    MeasurableSet {cv | argminIn Finset.univ (key cv) σ = i} := by
  have : {cv | argminIn Finset.univ (key cv) σ = i} =
      ⋂ j, ({cv | key cv i < key cv j} ∪ ({cv | key cv i = key cv j} ∩ {_cv | σ i ≤ σ j})) := by
    ext cv
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_inter_iff,
      argminIn_univ_eq_iff, LexLE]
  rw [this]
  exact MeasurableSet.iInter fun j => (measurableSet_lt (hk i) (hk j)).union
    ((measurableSet_eq_fun (hk i) (hk j)).inter (MeasurableSet.const _))

theorem card_perm_pos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem one_le_card_perm : (1 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem sum_ite_le_card [NeZero N] (p : Equiv.Perm (Fin N) → Prop) [DecidablePred p] :
    ∑ σ : Equiv.Perm (Fin N), (if p σ then (1 : ℝ) else 0) ≤
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
  calc ∑ σ : Equiv.Perm (Fin N), (if p σ then (1 : ℝ) else 0)
      ≤ ∑ _σ : Equiv.Perm (Fin N), (1 : ℝ) :=
        Finset.sum_le_sum fun σ _ => by split_ifs <;> norm_num
    _ = _ := by simp

theorem winProbFPA_nonneg [NeZero N] (v : Fin N → ℝ) (i : Fin N) : 0 ≤ winProbFPA v i := by
  unfold winProbFPA
  apply mul_nonneg (inv_nonneg.mpr card_perm_pos.le)
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem winProbFPA_le_one [NeZero N] (v : Fin N → ℝ) (i : Fin N) : winProbFPA v i ≤ 1 := by
  unfold winProbFPA
  rw [inv_mul_le_iff₀ card_perm_pos, mul_one]
  exact sum_ite_le_card _

/-- H1: strictly lowest bid wins for sure. -/
theorem winProbFPA_eq_one [NeZero N] (v : Fin N → ℝ) (i : Fin N)
    (h : ∀ j, j ≠ i → v i < v j) : winProbFPA v i = 1 := by
  unfold winProbFPA
  have : ∀ σ : Equiv.Perm (Fin N), argminIn Finset.univ v σ = i := by
    intro σ
    rw [argminIn_univ_eq_iff]
    intro j
    by_cases hj : j = i
    · subst hj; right; exact ⟨rfl, le_rfl⟩
    · left; exact h j hj
  simp only [this, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ card_perm_pos.ne'

/-- H3: someone bids strictly less, so `i` never wins. -/
theorem winProbFPA_eq_zero [NeZero N] (v : Fin N → ℝ) (i : Fin N) (j : Fin N)
    (h : v j < v i) : winProbFPA v i = 0 := by
  unfold winProbFPA
  have : ∀ σ : Equiv.Perm (Fin N), argminIn Finset.univ v σ ≠ i := by
    intro σ hσ
    rw [argminIn_univ_eq_iff] at hσ
    rcases hσ j with h' | ⟨h', _⟩ <;> linarith
  simp [this]

/-- H2: weakly lowest bid wins with probability at least `1/N!`. -/
theorem winProbFPA_ge [NeZero N] (v : Fin N → ℝ) (i : Fin N)
    (h : ∀ j, j ≠ i → v i ≤ v j) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ ≤ winProbFPA v i := by
  unfold winProbFPA
  rw [← mul_one ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹)]
  rw [mul_assoc, one_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr card_perm_pos.le)
  set σ0 : Equiv.Perm (Fin N) := Equiv.swap i 0
  have h0 : argminIn Finset.univ v σ0 = i := by
    rw [argminIn_univ_eq_iff]
    intro j
    by_cases hj : j = i
    · subst hj; right; exact ⟨rfl, le_rfl⟩
    · rcases (h j hj).lt_or_eq with hl | he
      · left; exact hl
      · right; refine ⟨he, ?_⟩
        simp only [σ0, Equiv.swap_apply_left]
        exact Fin.zero_le _
  calc (1 : ℝ) = if argminIn Finset.univ v σ0 = i then 1 else 0 := by rw [if_pos h0]
    _ ≤ _ := Finset.single_le_sum (f := fun σ => if argminIn Finset.univ v σ = i then (1:ℝ) else 0)
        (fun σ _ => by split_ifs <;> norm_num) (Finset.mem_univ σ0)

/-- H4: a tie with another bidder caps the winning probability at `1 - 1/N!`. -/
theorem winProbFPA_tie [NeZero N] (v : Fin N → ℝ) (i k : Fin N) (hki : k ≠ i)
    (h : v k = v i) :
    winProbFPA v i ≤ 1 - (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ := by
  obtain ⟨σ1, hσ1⟩ : ∃ σ1 : Equiv.Perm (Fin N), σ1 k < σ1 i := by
    rcases lt_or_gt_of_ne hki with hl | hl
    · exact ⟨1, hl⟩
    · refine ⟨Equiv.swap i k, ?_⟩
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]; exact hl
  have hne : argminIn Finset.univ v σ1 ≠ i := by
    intro hσ
    rw [argminIn_univ_eq_iff] at hσ
    rcases hσ k with h' | ⟨_, h'⟩
    · linarith
    · exact absurd h' (not_le.mpr hσ1)
  unfold winProbFPA
  have hK := card_perm_pos (N := N)
  have hsum : ∑ σ : Equiv.Perm (Fin N), (if argminIn Finset.univ v σ = i then (1 : ℝ) else 0) ≤
      ∑ σ : Equiv.Perm (Fin N), ((1 : ℝ) - if σ = σ1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro σ _
    by_cases hs : σ = σ1
    · subst hs; simp [hne]
    · simp only [hs, if_false, sub_zero]; split_ifs <;> norm_num
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hsum
  rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hK]
  rw [sub_mul, inv_mul_cancel₀ hK.ne', one_mul]
  exact hsum

/-! Model facts. -/

theorem costLaw_prob (P : Params N) (hS : P.Standing) (j : Fin N) :
    IsProbabilityMeasure (costLaw P j) := by
  obtain ⟨-, -, -, -, -, -, hfnn, hfm, -, hf1, -⟩ := hS
  constructor
  unfold costLaw fi
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_sub_right_eq_self (fun c => ENNReal.ofReal (P.f c)) (P.dc j)]
  have hint : Integrable P.f := Integrable.of_integral_ne_zero (by rw [hf1]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hfnn), hf1]
  simp

theorem costLaw_singleton (P : Params N) (j : Fin N) (x : ℝ) : costLaw P j {x} = 0 := by
  unfold costLaw
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

theorem costLaw_Icc_pos (P : Params N) (hS : P.Standing) (j : Fin N) (x1 x2 : ℝ)
    (h1 : cLoI P j ≤ x1) (h12 : x1 < x2) (h2 : x2 ≤ cHiI P j) :
    0 < costLaw P j (Set.Icc x1 x2) := by
  have hfm : Measurable P.f := hS.2.2.2.2.2.2.2.1
  have hfpos : ∀ x ∈ Set.Ioo P.cLo P.cHi, 0 < P.f x := hS.2.2.2.2.2.2.2.2.2.2.2.1
  unfold costLaw
  have hm : Measurable fun c => ENNReal.ofReal (fi P j c) :=
    (hfm.comp (measurable_id.sub_const _)).ennreal_ofReal
  rw [withDensity_apply _ measurableSet_Icc, setLIntegral_pos_iff hm]
  have hsub : Set.Ioo x1 x2 ⊆ Function.support (fun c => ENNReal.ofReal (fi P j c)) ∩
      Set.Icc x1 x2 := by
    intro c hc
    refine ⟨?_, Set.Ioo_subset_Icc_self hc⟩
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    unfold fi
    apply hfpos
    unfold cLoI at h1; unfold cHiI at h2
    constructor <;> linarith [hc.1, hc.2]
  calc (0 : ENNReal) < volume (Set.Ioo x1 x2) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
    _ ≤ _ := measure_mono hsub

theorem costLaw_ae_Ioo (P : Params N) (hS : P.Standing) (j : Fin N) :
    ∀ᵐ c ∂(costLaw P j), c ∈ Set.Ioo (cLoI P j) (cHiI P j) := by
  have hfm : Measurable P.f := hS.2.2.2.2.2.2.2.1
  have hfz : ∀ x, x ∉ Set.Icc P.cLo P.cHi → P.f x = 0 := hS.2.2.2.2.2.2.2.2.1
  unfold costLaw
  have hm : Measurable fun c => ENNReal.ofReal (fi P j c) :=
    (hfm.comp (measurable_id.sub_const _)).ennreal_ofReal
  rw [ae_withDensity_iff hm]
  have hne : ∀ a : ℝ, ∀ᵐ c ∂(volume : Measure ℝ), c ≠ a := by
    intro a; rw [ae_iff]; simp
  filter_upwards [hne (cLoI P j), hne (cHiI P j)] with c hc1 hc2 hc
  have hmem : c - P.dc j ∈ Set.Icc P.cLo P.cHi := by
    by_contra hcon
    apply hc
    unfold fi; rw [hfz _ hcon]; simp
  unfold cLoI cHiI at *
  constructor
  · rcases (show P.cLo + P.dc j ≤ c by linarith [hmem.1]).lt_or_eq with h | h
    · exact h
    · exact absurd h.symm hc1
  · rcases (show c ≤ P.cHi + P.dc j by linarith [hmem.2]).lt_or_eq with h | h
    · exact h
    · exact absurd h hc2

theorem costVecLaw_prob (P : Params N) (hS : P.Standing) : IsProbabilityMeasure (costVecLaw P) := by
  haveI := costLaw_prob P hS
  unfold costVecLaw; infer_instance

theorem costVecLaw_ae_ne (P : Params N) (hS : P.Standing) (j k : Fin N) (hjk : j ≠ k) :
    ∀ᵐ cv ∂(costVecLaw P), cv j ≠ cv k := by
  haveI := costLaw_prob P hS
  haveI := costVecLaw_prob P hS
  have hind : ProbabilityTheory.iIndepFun (fun j (cv : Fin N → ℝ) => cv j) (costVecLaw P) := by
    unfold costVecLaw
    exact ProbabilityTheory.iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have hjk' := hind.indepFun hjk
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply j).aemeasurable (measurable_pi_apply k).aemeasurable] at hjk'
  rw [ae_iff]
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  have hset : {cv : Fin N → ℝ | ¬ cv j ≠ cv k} =
      (fun cv : Fin N → ℝ => (cv j, cv k)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := by
    ext cv; simp
  rw [hset, ← Measure.map_apply (by fun_prop) hD, hjk', Measure.prod_apply hD]
  have hk : (costVecLaw P).map (fun cv => cv k) = costLaw P k := by
    unfold costVecLaw
    exact (measurePreserving_eval (costLaw P) k).map_eq
  rw [hk]
  have hx : ∀ x : ℝ, costLaw P k (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this]; exact costLaw_singleton P k x
  simp [costLaw_singleton]


theorem winProbBAI_eq_FPA [NeZero N] (P : Params N) (hsym : ExAnteSymmetric P)
    (v : Fin N → ℝ) (i : Fin N) : winProbBAI P v i = winProbFPA v i := by
  unfold winProbBAI winProbFPA argminIn
  have hr : ∀ j, rBAI P j = rBAI P 0 := fun j => by unfold rBAI; rw [(hsym j 0).2]
  have : (fun j => v j - rBAI P j) = fun j => v j - rBAI P 0 := funext fun j => by rw [hr j]
  rw [this]
  have hL : ∀ σ : Equiv.Perm (Fin N),
      LexLE (fun j => v j - rBAI P 0) σ = LexLE v σ := by
    intro σ; funext a b; simp [LexLE]
  simp only [hL]

/-- The main equilibrium step: a nondecreasing symmetric BAI equilibrium is strictly increasing
on the cost support whenever there are at least two suppliers. -/
theorem strictMono_of_eq [NeZero N] (P : Params N) (hS : P.Standing)
    (hsym : ExAnteSymmetric P) (βA : Fin N → ℝ → ℝ)
    (hA : IsEqBAI P βA) (hAsym : ∀ i j, βA i = βA j)
    (hAmono : ∀ i, MonotoneOn (βA i) (Set.Icc (cLoI P i) (cHiI P i)))
    (i k : Fin N) (hki : k ≠ i) :
    StrictMonoOn (βA i) (Set.Icc (cLoI P i) (cHiI P i)) := by
  haveI := costLaw_prob P hS
  haveI := costVecLaw_prob P hS
  set β := βA i with hβdef
  have hβ : ∀ j, βA j = β := fun j => hAsym j i
  have hLo : ∀ j, cLoI P j = cLoI P i := fun j => by unfold cLoI; rw [(hsym j i).1]
  have hHi : ∀ j, cHiI P j = cHiI P i := fun j => by unfold cHiI; rw [(hsym j i).1]
  have hβm : Measurable β := hA.1 i
  have hlast := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLo0 : 0 ≤ cLoI P i := by unfold cLoI; linarith [(hlast i).1]
  obtain ⟨-, hrange, hIC⟩ := hA
  set K : ℝ := (Fintype.card (Equiv.Perm (Fin N)) : ℝ) with hK
  have hKpos : 0 < K := card_perm_pos
  have hK1 : 1 ≤ K := one_le_card_perm
  by_contra hns
  unfold StrictMonoOn at hns
  push_neg at hns
  obtain ⟨x1, hx1, x2, hx2, hlt, hle⟩ := hns
  have heq : β x1 = β x2 := le_antisymm (hAmono i hx1 hx2 hlt.le) hle
  set b0 := β x1 with hb0
  have hconst : ∀ y ∈ Set.Icc x1 x2, β y = b0 := by
    intro y hy
    have hyI : y ∈ Set.Icc (cLoI P i) (cHiI P i) := ⟨le_trans hx1.1 hy.1, le_trans hy.2 hx2.2⟩
    exact le_antisymm (heq ▸ hAmono i hyI hx2 hy.2) (hAmono i hx1 hyI hy.1)
  -- the bid vector
  set g : ℝ → (Fin N → ℝ) → ℝ :=
    fun b cv => winProbBAI P (Function.update (bidProfile βA cv) i b) i with hg
  have hgFPA : ∀ b cv, g b cv = winProbFPA (Function.update (bidProfile βA cv) i b) i :=
    fun b cv => winProbBAI_eq_FPA P hsym _ _
  have hvi : ∀ b cv, Function.update (bidProfile βA cv) i b i = b := fun b cv => by simp
  have hvj : ∀ b cv j, j ≠ i → Function.update (bidProfile βA cv) i b j = β (cv j) := by
    intro b cv j hj
    rw [Function.update_of_ne hj]; simp [bidProfile, hβ j]
  have hg0 : ∀ b cv, 0 ≤ g b cv := fun b cv => by rw [hgFPA]; exact winProbFPA_nonneg _ _
  have hg1 : ∀ b cv, g b cv ≤ 1 := fun b cv => by rw [hgFPA]; exact winProbFPA_le_one _ _
  have hgm : ∀ b, Measurable (g b) := by
    intro b
    have hkey : ∀ j, Measurable fun cv : Fin N → ℝ => Function.update (bidProfile βA cv) i b j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; exact measurable_const
      · simp only [hvj b _ j hj]; exact hβm.comp (measurable_pi_apply j)
    have : g b = fun cv => (K)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
        Set.indicator {cv | argminIn Finset.univ (Function.update (bidProfile βA cv) i b) σ = i}
          (fun _ => (1 : ℝ)) cv := by
      funext cv; rw [hgFPA]; unfold winProbFPA; simp [Set.indicator, hK]
    rw [this]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro σ _
    exact measurable_const.indicator (measurableSet_argmin _ hkey σ i)
  have hgi : ∀ b, Integrable (g b) (costVecLaw P) := by
    intro b
    refine (integrable_const (1 : ℝ)).mono' (hgm b).aestronglyMeasurable (ae_of_all _ ?_)
    intro cv; rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [hg0 b cv], hg1 b cv⟩
  set W : ℝ → ℝ := fun b => ∫ cv, g b cv ∂(costVecLaw P) with hW
  have hprofit : ∀ b c, profitBAI P βA i b c = (b - c) * W b := fun b c => rfl
  -- sets
  set Bx : Set (Fin N → ℝ) :=
    Set.univ.pi (fun j => if j = i then Set.univ else Set.Icc x1 x2) with hBx
  set Ax : Set (Fin N → ℝ) :=
    Set.univ.pi (fun j => if j = i then Set.univ else β ⁻¹' Set.Ici b0) with hAx
  have hBxm : MeasurableSet Bx := by
    apply MeasurableSet.univ_pi; intro j; split_ifs
    · exact MeasurableSet.univ
    · exact measurableSet_Icc
  have hAxm : MeasurableSet Ax := by
    apply MeasurableSet.univ_pi; intro j; split_ifs
    · exact MeasurableSet.univ
    · exact hβm measurableSet_Ici
  have memB : ∀ cv, cv ∈ Bx ↔ ∀ j, j ≠ i → cv j ∈ Set.Icc x1 x2 := by
    intro cv; simp only [hBx, Set.mem_univ_pi]
    constructor
    · intro h j hj; have := h j; rwa [if_neg hj] at this
    · intro h j; split_ifs with hj
      · exact Set.mem_univ _
      · exact h j hj
  have memA : ∀ cv, cv ∈ Ax ↔ ∀ j, j ≠ i → b0 ≤ β (cv j) := by
    intro cv; simp only [hAx, Set.mem_univ_pi]
    constructor
    · intro h j hj; have := h j; rwa [if_neg hj] at this
    · intro h j; split_ifs with hj
      · exact Set.mem_univ _
      · exact h j hj
  have hBA : ∀ cv, cv ∈ Bx → cv ∈ Ax := by
    intro cv h; rw [memB] at h; rw [memA]
    intro j hj; rw [hconst _ (h j hj)]
  -- measure of the box
  set q : ℝ := (costVecLaw P).real Bx with hq
  have hqpos : 0 < q := by
    rw [hq, measureReal_def]
    apply ENNReal.toReal_pos
    · unfold costVecLaw; rw [hBx, Measure.pi_pi]
      rw [Finset.prod_ne_zero_iff]
      intro j _
      split_ifs with hj
      · simp
      · apply ne_of_gt
        apply costLaw_Icc_pos P hS j x1 x2 _ hlt _
        · rw [hLo j]; exact hx1.1
        · rw [hHi j]; exact hx2.2
    · exact measure_ne_top _ _
  have hq1 : q ≤ 1 := by rw [hq]; exact measureReal_le_one
  have hintB : ∫ cv, Bx.indicator (fun _ => (1 : ℝ)) cv ∂(costVecLaw P) = q := by
    rw [integral_indicator hBxm, setIntegral_const, smul_eq_mul, mul_one]
  set α : ℝ := ∫ cv, Ax.indicator (fun _ => (1 : ℝ)) cv ∂(costVecLaw P) with hα
  have hα1 : α ≤ 1 := by
    rw [hα, integral_indicator hAxm, setIntegral_const, smul_eq_mul, mul_one]
    exact measureReal_le_one
  have hα0 : 0 ≤ α := integral_nonneg fun cv => by
    simp only [Set.indicator]; split_ifs <;> norm_num
  have hIA : Integrable (Ax.indicator (fun _ => (1 : ℝ))) (costVecLaw P) :=
    (integrable_const (1 : ℝ)).indicator hAxm
  have hIB : Integrable (Bx.indicator (fun _ => (1 : ℝ))) (costVecLaw P) :=
    (integrable_const (1 : ℝ)).indicator hBxm
  -- (P3) lower bound at b0 on the box
  have hP3 : ∀ cv, K⁻¹ * Bx.indicator (fun _ => (1 : ℝ)) cv ≤ g b0 cv := by
    intro cv
    by_cases hc : cv ∈ Bx
    · rw [Set.indicator_of_mem hc, mul_one, hgFPA]
      apply winProbFPA_ge
      intro j hj
      rw [hvi, hvj _ _ _ hj, hconst _ ((memB cv).1 hc j hj)]
    · rw [Set.indicator_of_notMem hc, mul_zero]; exact hg0 _ _
  have hWlow : K⁻¹ * q ≤ W b0 := by
    rw [← hintB, ← integral_const_mul]
    exact integral_mono (hIB.const_mul _) (hgi b0) hP3
  have hW0 : ∀ b, 0 ≤ W b := fun b => integral_nonneg (hg0 b)
  by_cases hcase : x1 < b0
  · -- undercutting the pool is profitable
    set δ := b0 - x1 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set ε := δ * q / (2 * K) with hε
    have hεpos : 0 < ε := by positivity
    have hεle : ε ≤ δ / 2 := by
      rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    -- (P1)
    have hP1 : ∀ cv, Ax.indicator (fun _ => (1 : ℝ)) cv ≤ g (b0 - ε) cv := by
      intro cv
      by_cases hc : cv ∈ Ax
      · rw [Set.indicator_of_mem hc, hgFPA, winProbFPA_eq_one]
        intro j hj
        rw [hvi, hvj _ _ _ hj]
        have := (memA cv).1 hc j hj
        linarith
      · rw [Set.indicator_of_notMem hc]; exact hg0 _ _
    -- (P2)
    have hP2 : ∀ cv, g b0 cv ≤
        Ax.indicator (fun _ => (1 : ℝ)) cv - K⁻¹ * Bx.indicator (fun _ => (1 : ℝ)) cv := by
      intro cv
      by_cases hcB : cv ∈ Bx
      · rw [Set.indicator_of_mem hcB, Set.indicator_of_mem (hBA cv hcB), mul_one, hgFPA]
        apply winProbFPA_tie _ i k hki
        rw [hvi, hvj _ _ _ hki, hconst _ ((memB cv).1 hcB k hki)]
      · rw [Set.indicator_of_notMem hcB, mul_zero, sub_zero]
        by_cases hcA : cv ∈ Ax
        · rw [Set.indicator_of_mem hcA]; exact hg1 _ _
        · rw [Set.indicator_of_notMem hcA]
          rw [memA] at hcA; push_neg at hcA
          obtain ⟨j, hj, hjlt⟩ := hcA
          rw [hgFPA, winProbFPA_eq_zero _ i j]
          rw [hvi, hvj _ _ _ hj]; exact hjlt
    have hWε : α ≤ W (b0 - ε) := integral_mono hIA (hgi _) hP1
    have hWb0 : W b0 ≤ α - K⁻¹ * q := by
      have := integral_mono (hgi b0) (hIA.sub (hIB.const_mul _)) hP2
      simp only [Pi.sub_apply] at this
      rw [integral_sub hIA (hIB.const_mul _), integral_const_mul, hintB] at this
      exact this
    -- the equilibrium inequality at type x1, deviating to b0 - ε
    have hdev := hIC i x1 hx1 (b0 - ε) ⟨by linarith [hx1.1], by
      have := (hrange i x1 hx1).2; linarith⟩
    rw [hprofit, hprofit] at hdev
    have hdev' : (b0 - ε - x1) * α ≤ (b0 - x1) * (α - K⁻¹ * q) := by
      calc (b0 - ε - x1) * α ≤ (b0 - ε - x1) * W (b0 - ε) :=
            mul_le_mul_of_nonneg_left hWε (by linarith)
        _ ≤ (β x1 - x1) * W (β x1) := hdev
        _ ≤ (b0 - x1) * (α - K⁻¹ * q) := mul_le_mul_of_nonneg_left hWb0 (by linarith)
    have hKq : K⁻¹ * q = q / K := by rw [div_eq_inv_mul]
    rw [hKq] at hdev'
    have h1 : δ * (q / K) ≤ ε * α := by rw [hδ]; nlinarith
    have h2 : ε * α ≤ ε := by nlinarith
    have h3 : ε = δ * (q / K) / 2 := by rw [hε]; field_simp
    have h4 : 0 < δ * (q / K) := by positivity
    linarith
  · -- the pool lies weakly above its bid: the top of the pool loses money
    push_neg at hcase
    have hdev := hIC i x2 hx2 (cHiI P i) ⟨by linarith [hx2.1, hx2.2], le_rfl⟩
    rw [hprofit, hprofit, ← hβdef, ← heq] at hdev
    have hneg : b0 - x2 < 0 := by linarith
    have h1 : 0 ≤ (cHiI P i - x2) * W (cHiI P i) :=
      mul_nonneg (by linarith [hx2.2]) (hW0 _)
    have h2 : 0 < W b0 := lt_of_lt_of_le (by positivity) hWlow
    nlinarith

end PAWpw

open PAWpw in
theorem solution {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing)
    (hA1 : Assumption1 P) (hsym : ExAnteSymmetric P) (τ : ℝ) (βI βA : Fin N → ℝ → ℝ)
    (hA : IsEqBAI P βA) (hAsym : ∀ i j, βA i = βA j)
    (hAmono : ∀ i, MonotoneOn (βA i) (Set.Icc (cLoI P i) (cHiI P i))) :
    (∀ b : Fin N → ℝ, ∑ i, winProbBAI P b i = 1) ∧
    (∀ b t : Fin N → ℝ, ∑ i, allocBIA P τ b t i = 1) ∧
    (∀ᵐ cv ∂(costVecLaw P),
      ∑ i, winProbBAI P (bidProfile βA cv) i * (Fi P i (cv i) / fi P i (cv i)) =
        Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i))) ∧
    (∀ cv t : Fin N → ℝ,
      Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i)) ≤
        ∑ i, allocBIA P τ (bidProfile βI cv) t i * (Fi P i (cv i) / fi P i (cv i))) := by
  have hKpos := card_perm_pos (N := N)
  have part1 : ∀ b : Fin N → ℝ, ∑ i, winProbBAI P b i = 1 := by
    intro b
    unfold winProbBAI winProbFPA
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hKpos.ne'
  have part2 : ∀ b t : Fin N → ℝ, ∑ i, allocBIA P τ b t i = 1 := by
    intro b t
    unfold allocBIA
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hKpos.ne'
  refine ⟨part1, part2, ?_, ?_⟩
  · -- the a.e. identity
    have hdc : ∀ j k, P.dc j = P.dc k := fun j k => (hsym j k).1
    have hgood : ∀ᵐ cv ∂(costVecLaw P), (∀ j, cv j ∈ Set.Ioo (cLoI P j) (cHiI P j)) ∧
        ∀ j k, j ≠ k → cv j ≠ cv k := by
      haveI := costLaw_prob P hS
      have h1 : ∀ᵐ cv ∂(costVecLaw P), ∀ j, cv j ∈ Set.Ioo (cLoI P j) (cHiI P j) := by
        rw [ae_all_iff]
        intro j
        unfold costVecLaw
        exact (Measure.quasiMeasurePreserving_eval (costLaw P) j).ae (costLaw_ae_Ioo P hS j)
      have h2 : ∀ᵐ cv ∂(costVecLaw P), ∀ j k, j ≠ k → cv j ≠ cv k := by
        rw [ae_all_iff]; intro j
        rw [ae_all_iff]; intro k
        by_cases hjk : j = k
        · exact ae_of_all _ fun cv h => absurd hjk h
        · filter_upwards [costVecLaw_ae_ne P hS j k hjk] with cv hcv _ using hcv
      filter_upwards [h1, h2] with cv a b using ⟨a, b⟩
    filter_upwards [hgood] with cv hcv
    obtain ⟨hIoo, hdist⟩ := hcv
    obtain ⟨j0, -, hj0⟩ := Finset.univ.exists_min_image cv Finset.univ_nonempty
    have hcmp : ∀ k, k ≠ j0 → cv j0 < cv k := fun k hk =>
      lt_of_le_of_ne (hj0 k (Finset.mem_univ k)) (hdist j0 k (Ne.symm hk))
    have hbid : ∀ k, k ≠ j0 → bidProfile βA cv j0 < bidProfile βA cv k := by
      intro k hk
      have hsm := strictMono_of_eq P hS hsym βA hA hAsym hAmono j0 k hk
      have hm0 : cv j0 ∈ Set.Icc (cLoI P j0) (cHiI P j0) := Set.Ioo_subset_Icc_self (hIoo j0)
      have hmk : cv k ∈ Set.Icc (cLoI P j0) (cHiI P j0) := by
        have := Set.Ioo_subset_Icc_self (hIoo k)
        unfold cLoI cHiI at this ⊢; rw [hdc j0 k]; exact this
      unfold bidProfile; rw [hAsym k j0]
      exact hsm hm0 hmk (hcmp k hk)
    have hwin : ∀ i, winProbBAI P (bidProfile βA cv) i = if i = j0 then 1 else 0 := by
      intro i
      rw [winProbBAI_eq_FPA P hsym]
      split_ifs with hi
      · subst hi; exact winProbFPA_eq_one _ _ hbid
      · exact winProbFPA_eq_zero _ i j0 (hbid i hi)
    simp only [hwin, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply le_antisymm
    · apply Finset.le_inf'
      intro k _
      by_cases hk : k = j0
      · subst hk; exact le_rfl
      · have hmono := hA1 k
        have heqF : ∀ c, Fi P j0 c / fi P j0 c = Fi P k c / fi P k c := by
          intro c; unfold Fi fi; rw [hdc j0 k]
        rw [heqF]
        apply hmono _ (hIoo k) (le_of_lt (hcmp k hk))
        have := hIoo j0
        unfold cLoI cHiI at this ⊢; rw [← hdc j0 k]; exact this
    · exact Finset.inf'_le _ (Finset.mem_univ j0)
  · intro cv t
    have hsum := part2 (bidProfile βI cv) t
    have hnn : ∀ i, 0 ≤ allocBIA P τ (bidProfile βI cv) t i := by
      intro i; unfold allocBIA
      apply mul_nonneg (inv_nonneg.mpr hKpos.le)
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    calc Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i))
        = ∑ i, allocBIA P τ (bidProfile βI cv) t i *
            Finset.univ.inf' Finset.univ_nonempty (fun i => Fi P i (cv i) / fi P i (cv i)) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i)) (hnn i)
