-- Prove2me | solution 1 for PreAwardInvest.WinWin.ex_ante_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:57:43.27594+00:00
-- url     : https://prove2.me/submissions/661fc525-ecea-451e-bc8c-6041276114af

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



open PreAwardInvest.WinWin
open MeasureTheory

namespace PAWpw

variable {N : ℕ}

/-- Every fiber of `f` is measurable. -/
def FM {X D : Type*} [MeasurableSpace X] (f : X → D) : Prop := ∀ v, MeasurableSet {x | f x = v}

section FMlemmas
variable {X D E : Type*} [MeasurableSpace X]

theorem FM_const (v0 : D) : FM (fun _ : X => v0) := fun v => MeasurableSet.const _

theorem FM_comp [Countable D] {f : X → D} (hf : FM f) (g : D → E) : FM (fun x => g (f x)) := by
  intro v
  have : {x | g (f x) = v} = ⋃ e ∈ {e : D | g e = v}, {x | f x = e} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun e _ => hf e

theorem FM_bind [Countable D] {d : X → D} (hd : FM d) (F : D → X → E) (hF : ∀ e, FM (F e)) :
    FM (fun x => F (d x) x) := by
  intro v
  have : {x | F (d x) x = v} = ⋃ e : D, ({x | d x = e} ∩ {x | F e x = v}) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨d x, rfl, h⟩
    · rintro ⟨e, rfl, h⟩; exact h
  rw [this]
  exact MeasurableSet.iUnion fun e => (hd e).inter (hF e v)

theorem FM_ite {p : X → Prop} [DecidablePred p] (hp : MeasurableSet {x | p x}) {f g : X → D}
    (hf : FM f) (hg : FM g) : FM (fun x => if p x then f x else g x) := by
  intro v
  have : {x | (if p x then f x else g x) = v} =
      ({x | p x} ∩ {x | f x = v}) ∪ ({x | p x}ᶜ ∩ {x | g x = v}) := by
    ext x; by_cases h : p x <;> simp [h]
  rw [this]
  exact (hp.inter (hf v)).union (hp.compl.inter (hg v))

theorem measurableSet_lt_dep [Countable D] {d : X → D} (hd : FM d) (u : X → ℝ) (w : D → X → ℝ)
    (hu : Measurable u) (hw : ∀ e, Measurable (w e)) :
    MeasurableSet {x | u x < w (d x) x} := by
  have : {x | u x < w (d x) x} = ⋃ e : D, ({x | d x = e} ∩ {x | u x < w e x}) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨d x, rfl, h⟩
    · rintro ⟨e, rfl, h⟩; exact h
  rw [this]
  exact MeasurableSet.iUnion fun e => (hd e).inter (measurableSet_lt hu (hw e))

end FMlemmas

theorem measurable_inf' {X : Type*} [MeasurableSpace X] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (g : ι → X → ℝ) (hg : ∀ j, Measurable (g j)) :
    Measurable (fun x => s.inf' hs (fun j => g j x)) := by
  have : (fun x => s.inf' hs (fun j => g j x)) = s.inf' hs g := by
    funext x; rw [Finset.inf'_apply]
  rw [this]
  exact Finset.inf'_induction hs _ (fun _f hf _g hg => hf.inf hg) fun n _ => hg n

theorem FM_filter {X : Type*} [MeasurableSpace X] (p : Fin N → X → Prop)
    [∀ x, DecidablePred fun l => p l x] (hp : ∀ l, MeasurableSet {x | p l x}) :
    FM (fun x => Finset.univ.filter (fun l => p l x)) := by
  intro T
  have : {x | Finset.univ.filter (fun l => p l x) = T} = ⋂ l, {x | p l x ↔ l ∈ T} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [this]
  refine MeasurableSet.iInter fun l => ?_
  by_cases hl : l ∈ T
  · simp only [hl, iff_true]; exact hp l
  · simp only [hl, iff_false]; exact (hp l).compl

theorem FM_argminIn [NeZero N] {X : Type*} [MeasurableSpace X] (s : Finset (Fin N))
    (key : X → Fin N → ℝ) (hk : ∀ j, Measurable fun x => key x j) (σ : Equiv.Perm (Fin N)) :
    FM (fun x => argminIn s (key x) σ) := by
  by_cases hs : s.Nonempty
  · intro i
    by_cases hi : i ∈ s
    · have : {x | argminIn s (key x) σ = i} =
          ⋂ j ∈ s, ({x | key x i < key x j} ∪ ({x | key x i = key x j} ∩ {_x | σ i ≤ σ j})) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_inter_iff]
        constructor
        · intro h j hj
          have := (argminIn_spec s hs (key x) σ).2 j hj
          rw [h] at this; exact this
        · intro h
          exact argminIn_eq s (key x) σ i hi h
      rw [this]
      exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
        (measurableSet_lt (hk i) (hk j)).union
          ((measurableSet_eq_fun (hk i) (hk j)).inter (MeasurableSet.const _))
    · have : {x | argminIn s (key x) σ = i} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hi (h ▸ (argminIn_spec s hs (key x) σ).1)
      rw [this]; exact MeasurableSet.empty
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have : ∀ x, argminIn s (key x) σ = Classical.epsilon (fun _ : Fin N => False) := by
      intro x
      unfold argminIn
      congr 1
      funext i
      simp [hs']
    simp only [this]
    exact FM_const _

/-! ## Measurability of the BIA mechanism -/

section BIA
variable [NeZero N] (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N))
variable {X : Type*} [MeasurableSpace X] (b t : X → Fin N → ℝ)
  (hb : ∀ j, Measurable fun x => b x j) (ht : ∀ j, Measurable fun x => t x j)
include hb

theorem meas_mu (j : Fin N) : Measurable fun x => mu P τ (b x) j := by
  unfold mu; exact (hb j).sub_const _

theorem FM_rank (j : Fin N) : FM (fun x => rank P τ σ (b x) j) := by
  unfold rank
  apply FM_comp (g := fun T : Finset (Fin N) => T.card + 1)
  apply FM_filter
  intro l
  have h1 := meas_mu P τ b hb l
  have h2 := meas_mu P τ b hb j
  have : {x | mu P τ (b x) l < mu P τ (b x) j ∨
      (mu P τ (b x) l = mu P τ (b x) j ∧ σ l < σ j)} =
      {x | mu P τ (b x) l < mu P τ (b x) j} ∪
        ({x | mu P τ (b x) l = mu P τ (b x) j} ∩ {_x | σ l < σ j}) := by
    ext x; simp
  rw [this]
  exact (measurableSet_lt h1 h2).union ((measurableSet_eq_fun h1 h2).inter (MeasurableSet.const _))

theorem FM_Ntil : FM (fun x => Ntil P τ σ (b x)) := by
  have hp : ∀ n, MeasurableSet {x | n = N ∨ ∃ i, tauI P τ i = 0 ∧ rank P τ σ (b x) i = n + 1} := by
    intro n
    have : {x | n = N ∨ ∃ i, tauI P τ i = 0 ∧ rank P τ σ (b x) i = n + 1} =
        {_x | n = N} ∪ ⋃ i, ({_x | tauI P τ i = 0} ∩ {x | rank P τ σ (b x) i = n + 1}) := by
      ext x; simp
    rw [this]
    exact (MeasurableSet.const _).union
      (MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter (FM_rank P τ σ b hb i _))
  intro n
  have : {x | Ntil P τ σ (b x) = n} =
      {x | n = N ∨ ∃ i, tauI P τ i = 0 ∧ rank P τ σ (b x) i = n + 1} ∩
        ⋂ m ∈ Finset.range n,
          {x | m = N ∨ ∃ i, tauI P τ i = 0 ∧ rank P τ σ (b x) i = m + 1}ᶜ := by
    ext x
    simp only [Ntil, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
      Set.mem_compl_iff]
    rw [Nat.find_eq_iff]
  rw [this]
  exact (hp n).inter (MeasurableSet.biInter (Set.to_countable _) fun m _ => (hp m).compl)

theorem FM_Nbar : FM (fun x => Nbar P τ σ (b x)) := by
  unfold Nbar
  exact FM_comp (FM_Ntil P τ σ b hb) (fun n => min P.Nhat n)

include ht

theorem meas_updatedBid (I : Finset (Fin N)) (j : Fin N) :
    Measurable fun x => updatedBid (b x) (t x) I j := by
  unfold updatedBid
  by_cases hj : j ∈ I
  · simp only [hj, if_true]; exact (hb j).sub (ht j)
  · simp only [hj, if_false, sub_zero]; exact hb j

theorem FM_indexPolicy (I : Finset (Fin N)) :
    FM (fun x => indexPolicy P τ σ (b x) I (t x)) := by
  unfold indexPolicy
  have hmu := meas_mu P τ b hb
  have hA := FM_argminIn (Finset.univ \ I) (fun x => mu P τ (b x)) hmu σ
  have hinf : Measurable fun x =>
      Finset.univ.inf' Finset.univ_nonempty (updatedBid (b x) (t x) I) :=
    measurable_inf' _ _ (fun j x => updatedBid (b x) (t x) I j)
      (fun j => meas_updatedBid b t hb ht I j)
  apply FM_ite
  · have : {x | Nbar P τ σ (b x) ≤ I.card} =
        ⋃ n ∈ {n : ℕ | n ≤ I.card}, {x | Nbar P τ σ (b x) = n} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun n _ => FM_Nbar P τ σ b hb n
  · exact FM_const _
  · apply FM_ite (MeasurableSet.const _)
    · apply FM_ite
      · exact measurableSet_lt_dep hA _ (fun j x => mu P τ (b x) j) hinf hmu
      · exact FM_const _
      · exact FM_comp hA _
    · exact FM_const _

theorem FM_runInv (k : ℕ) : ∀ I : Finset (Fin N),
    FM (fun x => runInv (indexPolicy P τ σ) (b x) (t x) k I) := by
  induction k with
  | zero => intro I; simp only [runInv]; exact FM_const _
  | succ k ih =>
    intro I
    let F : Option (Fin N) → X → Finset (Fin N) := fun o x =>
      Option.elim o I (fun j => if j ∈ I then I else
        runInv (indexPolicy P τ σ) (b x) (t x) k (insert j I))
    have heq : ∀ x, runInv (indexPolicy P τ σ) (b x) (t x) (k + 1) I =
        F (indexPolicy P τ σ (b x) I (t x)) x := by
      intro x
      rcases hx : indexPolicy P τ σ (b x) I (t x) with _ | j <;> simp [runInv, hx, F]
    simp only [heq]
    have hF : ∀ o : Option (Fin N), FM (F o) := by
      intro o
      cases o with
      | none => exact FM_const _
      | some j =>
        by_cases hj : j ∈ I
        · simp only [F, Option.elim, hj, if_true]; exact FM_const _
        · simp only [F, Option.elim, hj, if_false]; exact ih _
    exact FM_bind (FM_indexPolicy P τ σ b t hb ht I) F hF

theorem FM_winnerBIA : FM (fun x => winnerBIA P τ σ (b x) (t x)) := by
  unfold winnerBIA investigated
  exact FM_bind (FM_runInv P τ σ b t hb ht P.Nhat ∅)
    (fun S x => argminIn Finset.univ (updatedBid (b x) (t x) S) σ)
    (fun S => FM_argminIn _ _ (fun j => meas_updatedBid b t hb ht S j) σ)

end BIA

theorem redLaw_prob (P : Params N) (hS : P.Standing) (j : Fin N) :
    IsProbabilityMeasure (redLaw P j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgnn, hgm, -, hg1, -⟩ := hS
  constructor
  unfold redLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_sub_right_eq_self (fun c => ENNReal.ofReal (P.g c)) (P.dt j)]
  have hint : Integrable P.g := Integrable.of_integral_ne_zero (by rw [hg1]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hgnn), hg1]
  simp

theorem measurable_winProbBIA [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ) (i : Fin N) :
    Measurable fun b : Fin N → ℝ => winProbBIA P τ b i := by
  haveI := redLaw_prob P hS
  haveI : IsProbabilityMeasure (redVecLaw P) := by unfold redVecLaw; infer_instance
  unfold winProbBIA
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro σ _
  apply Measurable.ennreal_toReal
  have hE : MeasurableSet {p : (Fin N → ℝ) × (Fin N → ℝ) | winnerBIA P τ σ p.1 p.2 = i} :=
    FM_winnerBIA P τ σ (fun p : (Fin N → ℝ) × (Fin N → ℝ) => p.1) (fun p => p.2)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp measurable_snd) i
  exact measurable_measure_prodMk_left hE

theorem measurable_winProbBAI [NeZero N] (P : Params N) (i : Fin N) :
    Measurable fun b : Fin N → ℝ => winProbBAI P b i := by
  unfold winProbBAI winProbFPA
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro σ _
  have hE := FM_argminIn (X := Fin N → ℝ) Finset.univ (fun b j => b j - rBAI P j)
    (fun j => (measurable_pi_apply j).sub_const _) σ i
  exact Measurable.ite hE measurable_const measurable_const

end PAWpw


open PreAwardInvest.WinWin
open MeasureTheory

/-- Abstract envelope theorem for a one-dimensional incentive-compatible direct mechanism. -/
theorem paw_envelope_abstract (W β : ℝ → ℝ) (lo hi : ℝ)
    (hIC : ∀ c ∈ Set.Icc lo hi, ∀ z ∈ Set.Icc lo hi,
      (β z - c) * W (β z) ≤ (β c - c) * W (β c)) :
    ∀ c ∈ Set.Icc lo hi,
      (β c - c) * W (β c) = (β hi - hi) * W (β hi) + ∫ y in c..hi, W (β y) := by
  set φ : ℝ → ℝ := fun y => W (β y) with hφ
  set U : ℝ → ℝ := fun c => (β c - c) * φ c with hU
  -- monotonicity of the allocation
  have hanti : AntitoneOn φ (Set.Icc lo hi) := by
    intro c hc z hz hcz
    have h1 := hIC c hc z hz
    have h2 := hIC z hz c hc
    simp only [hφ] at *
    rcases eq_or_lt_of_le hcz with h | h
    · rw [h]
    · nlinarith
  -- two-sided bounds on profit differences
  have hUlow : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi,
      (b - a) * φ b ≤ U a - U b := by
    intro a ha b hb
    have := hIC a ha b hb
    simp only [hU, hφ] at *; nlinarith
  have hUup : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi,
      U a - U b ≤ (b - a) * φ a := by
    intro a ha b hb
    have := hIC b hb a ha
    simp only [hU, hφ] at *; nlinarith
  have hII : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, IntervalIntegrable φ volume a b := by
    intro a ha b hb
    apply AntitoneOn.intervalIntegrable
    apply hanti.mono
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans ha.1 h1, le_trans h2 hb.2⟩
    · exact ⟨le_trans hb.1 h1, le_trans h2 ha.2⟩
  have hIlow : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      (b - a) * φ b ≤ ∫ y in a..b, φ y := by
    intro a ha b hb hab
    have : ∫ y in a..b, φ b ≤ ∫ y in a..b, φ y := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hII a ha b hb)
      intro x hx
      exact hanti ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩ hb hx.2
    simpa [intervalIntegral.integral_const] using this
  have hIup : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      ∫ y in a..b, φ y ≤ (b - a) * φ a := by
    intro a ha b hb hab
    have : ∫ y in a..b, φ y ≤ ∫ y in a..b, φ a := by
      apply intervalIntegral.integral_mono_on hab (hII a ha b hb) intervalIntegrable_const
      intro x hx
      exact hanti ha ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩ hx.1
    simpa [intervalIntegral.integral_const] using this
  set D : ℝ → ℝ → ℝ := fun a b => (U a - U b) - ∫ y in a..b, φ y with hD
  have hDbd : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      |D a b| ≤ (b - a) * (φ a - φ b) := by
    intro a ha b hb hab
    have h1 := hUlow a ha b hb
    have h2 := hUup a ha b hb
    have h3 := hIlow a ha b hb hab
    have h4 := hIup a ha b hb hab
    rw [abs_le]; simp only [hD]; constructor <;> nlinarith
  have hDadd : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, ∀ e ∈ Set.Icc lo hi,
      D a e = D a b + D b e := by
    intro a ha b hb e he
    simp only [hD]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII a ha b hb) (hII b hb e he)]
    ring
  intro c hc
  have hchi : c ≤ hi := hc.2
  have hhi : hi ∈ Set.Icc lo hi := ⟨le_trans hc.1 hc.2, le_rfl⟩
  suffices hD0 : D c hi = 0 by
    simp only [hD, hU] at hD0; linarith
  -- partition argument
  have key : ∀ n : ℕ, 0 < n → |D c hi| ≤ (hi - c) / n * (φ c - φ hi) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (hi - c) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (by linarith) hnpos.le
    have hxmem : ∀ m : ℕ, m ≤ n → c + m * h ∈ Set.Icc lo hi := by
      intro m hm
      have hm' : (m : ℝ) ≤ n := by exact_mod_cast hm
      have : (m : ℝ) * h ≤ hi - c := by
        rw [hh, mul_div_assoc']
        rw [div_le_iff₀ hnpos]; nlinarith
      exact ⟨by nlinarith [hc.1], by linarith⟩
    have ind : ∀ m : ℕ, m ≤ n → |D c (c + m * h)| ≤ h * (φ c - φ (c + m * h)) := by
      intro m
      induction m with
      | zero =>
        intro _
        simp [hD]
      | succ m ih =>
        intro hm
        have hm1 : m ≤ n := Nat.le_of_succ_le hm
        have hx := hxmem m hm1
        have hx1 := hxmem (m + 1) hm
        have hsplit := hDadd c hc _ hx _ hx1
        have hb := hDbd _ hx _ hx1 (by push_cast; nlinarith)
        have ih' := ih hm1
        rw [hsplit]
        calc |D c (c + ↑m * h) + D (c + ↑m * h) (c + ↑(m + 1) * h)|
            ≤ |D c (c + ↑m * h)| + |D (c + ↑m * h) (c + ↑(m + 1) * h)| := abs_add_le _ _
          _ ≤ h * (φ c - φ (c + ↑m * h)) +
              (c + ↑(m + 1) * h - (c + ↑m * h)) * (φ (c + ↑m * h) - φ (c + ↑(m + 1) * h)) :=
              add_le_add ih' hb
          _ = h * (φ c - φ (c + ↑(m + 1) * h)) := by push_cast; ring
    have := ind n le_rfl
    have hend : c + (n : ℝ) * h = hi := by
      rw [hh]; field_simp; ring
    rw [hend] at this
    linarith
  -- conclude
  have hφnn : 0 ≤ φ c - φ hi := by
    have := hanti hc hhi hchi; linarith
  by_contra hne
  have hpos : 0 < |D c hi| := abs_pos.mpr hne
  set K := (hi - c) * (φ c - φ hi) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by linarith) hφnn
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |D c hi|)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hK0 hpos.le) hn
    exact_mod_cast this
  have hk := key n hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have : (hi - c) / n * (φ c - φ hi) = K / n := by rw [hK]; ring
  rw [this, le_div_iff₀ hnpos] at hk
  rw [div_lt_iff₀ hpos] at hn
  linarith


namespace PAWpw

variable {N : ℕ}

section Dist
variable (P : Params N) (hS : P.Standing)
include hS

theorem f_integrable : Integrable P.f := Integrable.of_integral_ne_zero (by rw [hS.2.2.2.2.2.2.2.2.2.1]; norm_num)

theorem Fc_nonneg (x : ℝ) : 0 ≤ Fc P x :=
  setIntegral_nonneg measurableSet_Iic fun y _ => hS.2.2.2.2.2.2.1 y

theorem Fc_le_one (x : ℝ) : Fc P x ≤ 1 := by
  unfold Fc; rw [← hS.2.2.2.2.2.2.2.2.2.1]
  exact setIntegral_le_integral (f_integrable P hS) (ae_of_all _ hS.2.2.2.2.2.2.1)

theorem Fc_mono : Monotone (Fc P) := fun x y hxy =>
  setIntegral_mono_set (f_integrable P hS).integrableOn (ae_of_all _ hS.2.2.2.2.2.2.1)
    (Set.Iic_subset_Iic.mpr hxy).eventuallyLE

theorem fi_nonneg (i : Fin N) (c : ℝ) : 0 ≤ fi P i c := hS.2.2.2.2.2.2.1 _

theorem fi_meas (i : Fin N) : Measurable (fi P i) :=
  hS.2.2.2.2.2.2.2.1.comp (measurable_id.sub_const _)

theorem h_meas (i : Fin N) : Measurable (fun c => Fi P i c / fi P i c) :=
  ((Fc_mono P hS).measurable.comp (measurable_id.sub_const _)).div (fi_meas P hS i)

theorem h_nonneg (i : Fin N) (c : ℝ) : 0 ≤ Fi P i c / fi P i c :=
  div_nonneg (Fc_nonneg P hS _) (fi_nonneg P hS i c)

theorem fi_zero_off (i : Fin N) (c : ℝ) (hc : c ∉ Set.Icc (cLoI P i) (cHiI P i)) :
    fi P i c = 0 := by
  unfold fi; apply hS.2.2.2.2.2.2.2.2.1
  intro h; apply hc; unfold cLoI cHiI; constructor <;> linarith [h.1, h.2]

theorem integral_Iic_fi (i : Fin N) (y : ℝ) : ∫ c in Set.Iic y, fi P i c = Fi P i y := by
  unfold Fi Fc fi
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  rw [← integral_sub_right_eq_self (μ := volume)
    (fun x => (Set.Iic (y - P.dc i)).indicator P.f x) (P.dc i)]
  congr 1; funext c
  simp only [Set.indicator, Set.mem_Iic, sub_le_sub_iff_right]

theorem costLaw_real_Iio (i : Fin N) (y : ℝ) : (costLaw P i).real (Set.Iio y) = Fi P i y := by
  haveI : NullSingletonClass (costLaw P i) := ⟨costLaw_singleton P i⟩
  rw [measureReal_def, measure_congr Iio_ae_eq_Iic]
  unfold costLaw
  rw [withDensity_apply _ measurableSet_Iic]
  have hint : Integrable (fi P i) := (f_integrable P hS).comp_sub_right _
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (ae_of_all _ fun c => fi_nonneg P hS i c)]
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun c _ => fi_nonneg P hS i c)]
  exact integral_Iic_fi P hS i y

theorem h_integrable (i : Fin N) : Integrable (fun c => Fi P i c / fi P i c) (costLaw P i) := by
  refine ⟨(h_meas P hS i).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral costLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ (fi_meas P hS i).ennreal_ofReal
    (h_meas P hS i).enorm]
  have hb : ∀ c, ((fun c => ENNReal.ofReal (fi P i c)) * fun c => ‖Fi P i c / fi P i c‖ₑ) c ≤
      (Set.Icc (cLoI P i) (cHiI P i)).indicator (fun _ => (1 : ENNReal)) c := by
    intro c
    simp only [Pi.mul_apply]
    rw [Real.enorm_eq_ofReal (h_nonneg P hS i c), ← ENNReal.ofReal_mul (fi_nonneg P hS i c)]
    by_cases hc : c ∈ Set.Icc (cLoI P i) (cHiI P i)
    · rw [Set.indicator_of_mem hc, ENNReal.ofReal_le_one]
      by_cases h0 : fi P i c = 0
      · rw [h0]; norm_num
      · rw [mul_div_cancel₀ _ h0]; exact Fc_le_one P hS _
    · rw [Set.indicator_of_notMem hc, fi_zero_off P hS i c hc]; simp
  calc _ ≤ ∫⁻ c, (Set.Icc (cLoI P i) (cHiI P i)).indicator (fun _ => (1 : ENNReal)) c :=
        lintegral_mono hb
    _ = volume (Set.Icc (cLoI P i) (cHiI P i)) := by
        rw [lintegral_indicator measurableSet_Icc]; simp
    _ < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top

end Dist

theorem bidProfile_update (βv : Fin N → ℝ → ℝ) (cv : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    bidProfile βv (Function.update cv i y) = Function.update (bidProfile βv cv) i (βv i y) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [bidProfile]
  · simp [bidProfile, Function.update_of_ne hj]

theorem update_measurePreserving (P : Params N) (hS : P.Standing) (i : Fin N) :
    MeasurePreserving (fun p : ℝ × (Fin N → ℝ) => Function.update p.2 i p.1)
      ((costLaw P i).prod (costVecLaw P)) (costVecLaw P) := by
  haveI := costLaw_prob P hS
  haveI := costVecLaw_prob P hS
  have hTm : Measurable (fun p : ℝ × (Fin N → ℝ) => Function.update p.2 i p.1) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact measurable_fst
    · simp only [Function.update_of_ne hj]; exact (measurable_pi_apply j).comp measurable_snd
  refine ⟨hTm, ?_⟩
  symm
  unfold costVecLaw
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hTm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : ℝ × (Fin N → ℝ) => Function.update p.2 i p.1) ⁻¹' Set.univ.pi s =
      s i ×ˢ Set.univ.pi (Function.update s i Set.univ) := by
    ext ⟨y, cv⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j; simp only [Function.update_of_ne hj] at this ⊢; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · have := h2 j; simp only [Function.update_of_ne hj] at this ⊢; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ j, costLaw P j (Function.update s i Set.univ j) =
      Function.update (fun j => costLaw P j (s j)) i 1 j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.prod_eq_mul_prod_sdiff_singleton i _ (fun h => absurd (Finset.mem_univ i) h)]

/-- The generic ex ante identity (Myerson) for an incentive compatible profile. -/
theorem exante_generic [NeZero N] (P : Params N) (hS : P.Standing) (i : Fin N)
    (βv : Fin N → ℝ → ℝ) (hβm : ∀ j, Measurable (βv j))
    (Q : (Fin N → ℝ) → ℝ) (hQm : Measurable Q) (hQ0 : ∀ b, 0 ≤ Q b) (hQ1 : ∀ b, Q b ≤ 1)
    (hIC : ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i), ∀ z ∈ Set.Icc (cLoI P i) (cHiI P i),
      (βv i z - c) * (∫ cv, Q (Function.update (bidProfile βv cv) i (βv i z)) ∂(costVecLaw P)) ≤
      (βv i c - c) * (∫ cv, Q (Function.update (bidProfile βv cv) i (βv i c)) ∂(costVecLaw P))) :
    ∫ c, (βv i c - c) * (∫ cv, Q (Function.update (bidProfile βv cv) i (βv i c)) ∂(costVecLaw P))
        ∂(costLaw P i) =
      (βv i (cHiI P i) - cHiI P i) *
          (∫ cv, Q (Function.update (bidProfile βv cv) i (βv i (cHiI P i))) ∂(costVecLaw P)) +
        ∫ cv, Q (bidProfile βv cv) * (Fi P i (cv i) / fi P i (cv i)) ∂(costVecLaw P) := by
  haveI := costLaw_prob P hS
  haveI := costVecLaw_prob P hS
  set μ := costLaw P i with hμ
  set π := costVecLaw P with hπ
  set lo := cLoI P i with hlo
  set hi := cHiI P i with hhi
  set β := βv i with hβ
  have hlohi : lo ≤ hi := by
    rw [hlo, hhi]; unfold cLoI cHiI; linarith [hS.2.2.2.2.1]
  set W : ℝ → ℝ := fun b => ∫ cv, Q (Function.update (bidProfile βv cv) i b) ∂π with hW
  have hJ : Measurable (fun p : ℝ × (Fin N → ℝ) =>
      Q (Function.update (bidProfile βv p.2) i p.1)) := by
    apply hQm.comp
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact measurable_fst
    · simp only [Function.update_of_ne hj, bidProfile]
      exact (hβm j).comp ((measurable_pi_apply j).comp measurable_snd)
  have hWm : Measurable W :=
    (hJ.stronglyMeasurable.integral_prod_right' (ν := π)).measurable
  have hW0 : ∀ b, 0 ≤ W b := fun b => integral_nonneg fun _ => hQ0 _
  have hW1 : ∀ b, W b ≤ 1 := by
    intro b
    calc W b ≤ ∫ _cv, (1 : ℝ) ∂π := by
          apply integral_mono_of_nonneg (ae_of_all _ fun _ => hQ0 _) (integrable_const _)
            (ae_of_all _ fun _ => hQ1 _)
      _ = 1 := by simp
  set φ : ℝ → ℝ := fun y => W (β y) with hφ
  have hφm : Measurable φ := hWm.comp (hβm i)
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => hW0 _
  have hφ1 : ∀ y, φ y ≤ 1 := fun y => hW1 _
  have hφII : ∀ a b, IntervalIntegrable φ volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hφm.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    show ‖φ y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]; exact hφ1 y
  have env := paw_envelope_abstract W β lo hi hIC
  set Φ : ℝ → ℝ := fun c => ∫ y in c..hi, φ y with hΦ
  have hΦc : Continuous Φ := by
    have := intervalIntegral.continuous_primitive hφII hi
    have heq : Φ = fun c => -∫ y in hi..c, φ y := by
      funext c; simp only [hΦ]; rw [intervalIntegral.integral_symm]
    rw [heq]; exact this.neg
  have haeI : ∀ᵐ c ∂μ, c ∈ Set.Icc lo hi := by
    filter_upwards [costLaw_ae_Ioo P hS i] with c hc using Set.Ioo_subset_Icc_self hc
  have hΦint : Integrable Φ μ := by
    refine (integrable_const (hi - lo)).mono' hΦc.aestronglyMeasurable ?_
    filter_upwards [haeI] with c hc
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := hi) (C := 1)
      (f := φ) (fun y _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]; exact hφ1 y)
    rw [abs_of_nonneg (by linarith [hc.2])] at this
    linarith [hc.1]
  -- Step A
  have stepA : ∫ c, (β c - c) * W (β c) ∂μ = (β hi - hi) * W (β hi) + ∫ c, Φ c ∂μ := by
    rw [integral_congr_ae (g := fun c => (β hi - hi) * W (β hi) + Φ c)]
    · rw [integral_add (integrable_const _) hΦint, integral_const]; simp
    · filter_upwards [haeI] with c hc using env c hc
  -- Step B
  set ν := volume.restrict (Set.Icc lo hi) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp [Real.volume_Icc])
  set G : ℝ → ℝ → ℝ := fun c y => if c < y then φ y else 0 with hG
  have hGint : Integrable (Function.uncurry G) (μ.prod ν) := by
    have hm : Measurable (Function.uncurry G) := by
      change Measurable fun p : ℝ × ℝ => if p.1 < p.2 then φ p.2 else 0
      exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        (hφm.comp measurable_snd) measurable_const
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    change ‖if p.1 < p.2 then φ p.2 else 0‖ ≤ 1
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]; exact hφ1 _
    · simp
  have stepB : ∫ c, Φ c ∂μ = ∫ y in Set.Icc lo hi, φ y * Fi P i y := by
    have h1 : ∫ c, Φ c ∂μ = ∫ c, ∫ y, G c y ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [haeI] with c hc
      show (∫ y in c..hi, φ y) = ∫ y, (if c < y then φ y else 0) ∂(volume.restrict (Set.Icc lo hi))
      rw [intervalIntegral.integral_of_le hc.2]
      have : (fun y => if c < y then φ y else 0) = (Set.Ioi c).indicator φ := by
        funext y; simp [Set.indicator]
      have hset : Set.Icc lo hi ∩ Set.Ioi c = Set.Ioc c hi := by
        ext y; simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi]
        constructor
        · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [hc.1], h2⟩, h1⟩
      rw [this, setIntegral_indicator measurableSet_Ioi, hset]
    rw [h1, integral_integral_swap hGint]
    apply integral_congr_ae
    filter_upwards with y
    have : (fun c => G c y) = (Set.Iio y).indicator (fun _ => φ y) := by
      funext c; simp [hG, Set.indicator]
    rw [this, integral_indicator_const _ measurableSet_Iio, costLaw_real_Iio P hS i y,
      smul_eq_mul, mul_comm]
  -- Step C
  have stepC : ∫ y in Set.Icc lo hi, φ y * Fi P i y =
      ∫ y, φ y * (Fi P i y / fi P i y) ∂μ := by
    have hμ' : μ = volume.withDensity (fun c => ((fi P i c).toNNReal : ENNReal)) := rfl
    rw [hμ', integral_withDensity_eq_integral_smul (f := fun c => (fi P i c).toNNReal)
      (measurable_real_toNNReal.comp (fi_meas P hS i))]
    have h2 : ∀ y, (fi P i y).toNNReal • (φ y * (Fi P i y / fi P i y)) =
        fi P i y * (φ y * (Fi P i y / fi P i y)) := by
      intro y; rw [NNReal.smul_def, Real.coe_toNNReal _ (fi_nonneg P hS i y), smul_eq_mul]
    simp only [h2]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc lo hi)
      (f := fun y => fi P i y * (φ y * (Fi P i y / fi P i y))) (fun y hy => by rw [fi_zero_off P hS i y hy, zero_mul])]
    rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    have hpos : 0 < fi P i y := by
      unfold fi
      apply hS.2.2.2.2.2.2.2.2.2.2.2.1
      have := hy; rw [hlo, hhi] at this; unfold cLoI cHiI at this
      constructor <;> linarith [this.1, this.2]
    simp only
    field_simp
  -- Step D
  have stepD : ∫ y, φ y * (Fi P i y / fi P i y) ∂μ =
      ∫ cv, Q (bidProfile βv cv) * (Fi P i (cv i) / fi P i (cv i)) ∂π := by
    have hT : MeasurePreserving (fun p : ℝ × (Fin N → ℝ) => Function.update p.2 i p.1)
        (μ.prod π) π := update_measurePreserving P hS i
    have hRm : Measurable (fun cv : Fin N → ℝ =>
        Q (bidProfile βv cv) * (Fi P i (cv i) / fi P i (cv i))) := by
      apply Measurable.mul
      · apply hQm.comp; apply measurable_pi_lambda; intro j
        exact (hβm j).comp (measurable_pi_apply j)
      · exact (h_meas P hS i).comp (measurable_pi_apply i)
    rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hRm.aestronglyMeasurable]
    have hK : ∀ p : ℝ × (Fin N → ℝ),
        Q (bidProfile βv (Function.update p.2 i p.1)) *
          (Fi P i (Function.update p.2 i p.1 i) / fi P i (Function.update p.2 i p.1 i)) =
        Q (Function.update (bidProfile βv p.2) i (β p.1)) * (Fi P i p.1 / fi P i p.1) := by
      intro p; rw [bidProfile_update]; simp [hβ]
    simp only [hK]
    have hKint : Integrable (fun p : ℝ × (Fin N → ℝ) =>
        Q (Function.update (bidProfile βv p.2) i (β p.1)) * (Fi P i p.1 / fi P i p.1))
        (μ.prod π) := by
      have hm : Measurable (fun p : ℝ × (Fin N → ℝ) =>
          Q (Function.update (bidProfile βv p.2) i (β p.1)) * (Fi P i p.1 / fi P i p.1)) := by
        apply Measurable.mul
        · exact hJ.comp (((hβm i).comp measurable_fst).prodMk measurable_snd)
        · exact (h_meas P hS i).comp measurable_fst
      have hb := (h_integrable P hS i).mul_prod (integrable_const (1 : ℝ) (μ := π))
      refine hb.mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
      simp only [mul_one]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQ0 _), abs_of_nonneg (h_nonneg P hS i _)]
      exact mul_le_of_le_one_left (h_nonneg P hS i _) (hQ1 _)
    rw [integral_prod _ hKint]
    apply integral_congr_ae
    filter_upwards with y
    simp only [hφ, hW]
    rw [integral_mul_const]
  rw [stepA, stepB, stepC, stepD]

end PAWpw


open PreAwardInvest.WinWin
open MeasureTheory

namespace PAWpw

theorem winProbBIA_nonneg {N : ℕ} [NeZero N] (P : Params N) (τ : ℝ) (b : Fin N → ℝ) (i : Fin N) :
    0 ≤ winProbBIA P τ b i := by
  unfold winProbBIA
  exact mul_nonneg (inv_nonneg.mpr card_perm_pos.le)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem winProbBIA_le_one {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ)
    (b : Fin N → ℝ) (i : Fin N) : winProbBIA P τ b i ≤ 1 := by
  haveI := redLaw_prob P hS
  haveI : IsProbabilityMeasure (redVecLaw P) := by unfold redVecLaw; infer_instance
  unfold winProbBIA
  rw [inv_mul_le_iff₀ card_perm_pos, mul_one]
  calc ∑ σ : Equiv.Perm (Fin N), ((redVecLaw P) {t | winnerBIA P τ σ b t = i}).toReal
      ≤ ∑ _σ : Equiv.Perm (Fin N), (1 : ℝ) :=
        Finset.sum_le_sum fun σ _ => by
          rw [← measureReal_def]; exact measureReal_le_one
    _ = _ := by simp

theorem winProbBAI_nonneg {N : ℕ} [NeZero N] (P : Params N) (b : Fin N → ℝ) (i : Fin N) :
    0 ≤ winProbBAI P b i := winProbFPA_nonneg _ _

theorem winProbBAI_le_one {N : ℕ} [NeZero N] (P : Params N) (b : Fin N → ℝ) (i : Fin N) :
    winProbBAI P b i ≤ 1 := winProbFPA_le_one _ _

end PAWpw

open PAWpw in
theorem solution {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i,
      exAnteBIA P τ βI i =
        profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) +
          ∫ cv, winProbBIA P τ (bidProfile βI cv) i * (Fi P i (cv i) / fi P i (cv i))
            ∂(costVecLaw P)) ∧
    (IsEqBAI P βA → ∀ i,
      exAnteBAI P βA i =
        profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) +
          ∫ cv, winProbBAI P (bidProfile βA cv) i * (Fi P i (cv i) / fi P i (cv i))
            ∂(costVecLaw P)) := by
  constructor
  · rintro ⟨hm, hrange, hIC⟩ i
    unfold exAnteBIA profitBIA
    exact exante_generic P hS i βI hm (fun b => winProbBIA P τ b i)
      (measurable_winProbBIA P hS τ i) (fun b => winProbBIA_nonneg P τ b i)
      (fun b => winProbBIA_le_one P hS τ b i)
      (fun c hc z hz => hIC i c hc (βI i z) (hrange i z hz))
  · rintro ⟨hm, hrange, hIC⟩ i
    unfold exAnteBAI profitBAI
    exact exante_generic P hS i βA hm (fun b => winProbBAI P b i)
      (measurable_winProbBAI P i) (fun b => winProbBAI_nonneg P b i)
      (fun b => winProbBAI_le_one P b i)
      (fun c hc z hz => hIC i c hc (βA i z) (hrange i z hz))
