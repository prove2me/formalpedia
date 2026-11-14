-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_a_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:28:01.03568+00:00
-- url     : https://prove2.me/submissions/4e458466-9619-407b-8016-162e2fc1e525

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing
import Theorems.Thm_BorsukUlam_exists_eq_neg

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-- The `k`-th largest entry (1-based) of a finite family: the largest minimum over `k`-subsets. -/
def ostat {B : ℕ} (k : ℕ) (D : Fin B → ℝ) : ℝ :=
  ⨆ S : (univ.powersetCard k : Finset (Finset (Fin B))), ⨅ v : (S : Finset (Fin B)), D v

/-- The polynomial with coefficient vector `z`. -/
def polyEval {d : ℕ} (z : Fin (d + 1) → ℝ) (x : ℝ) : ℝ := ∑ a, z a * x ^ (a : ℕ)

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.LA2
open Finset Filter Topology
lemma ostat_eq_of {B k : ℕ} (D : Fin B → ℝ) (c : ℝ) (S0 : Finset (Fin B)) (hS0 : S0.card = k)
    (h0 : ∀ v ∈ S0, c ≤ D v) (h1 : ∀ S : Finset (Fin B), S.card = k → ∃ v ∈ S, D v ≤ c) :
    ostat k D = c := by
  unfold ostat
  have hm : S0 ∈ (univ : Finset (Fin B)).powersetCard k :=
    mem_powersetCard.2 ⟨subset_univ _, hS0⟩
  have : Nonempty ((univ : Finset (Fin B)).powersetCard k) := ⟨⟨S0, hm⟩⟩
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨S, hS⟩
    obtain ⟨v, hv, hvc⟩ := h1 S (mem_powersetCard.1 hS).2
    exact (ciInf_le (Set.finite_range _).bddBelow ⟨v, hv⟩).trans hvc
  · obtain ⟨v0, hv0, -⟩ := h1 S0 hS0
    have : Nonempty S0 := ⟨⟨v0, hv0⟩⟩
    refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨S0, hm⟩ ?_
    exact le_ciInf fun v => h0 v v.2

/-- A ranking of the bins realising the order statistics. -/
theorem ostat_sorted {B : ℕ} (D : Fin B → ℝ) :
    ∃ rk : Fin B ≃ Fin B, (∀ r : Fin B, D (rk.symm r) = ostat (r.val + 1) D) ∧
      ∀ r r' : Fin B, r ≤ r' → D (rk.symm r') ≤ D (rk.symm r) := by
  set σ := Tuple.sort (fun v => -D v) with hσ
  have hmono := Tuple.monotone_sort (fun v => -D v)
  have anti : ∀ r r' : Fin B, r ≤ r' → D (σ r') ≤ D (σ r) := by
    intro r r' h
    have := hmono h
    simp only [Function.comp] at this
    linarith
  refine ⟨σ.symm, ?_, ?_⟩
  · intro r
    simp only [Equiv.symm_symm]
    symm
    refine ostat_eq_of D (D (σ r)) ((Iic r).map σ.toEmbedding) ?_ ?_ ?_
    · rw [card_map, Fin.card_Iic]
    · intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hv
      exact anti i r (mem_Iic.1 hi)
    · intro S hS
      have hlt : (Iio r).card < (S.map σ.symm.toEmbedding).card := by
        rw [card_map, Fin.card_Iio, hS]; omega
      obtain ⟨e, he, hne⟩ := exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨v, hv, rfl⟩ := mem_map.1 he
      refine ⟨v, hv, ?_⟩
      have hre : r ≤ σ.symm v := by
        simpa [mem_Iio, not_lt] using hne
      have := anti r (σ.symm v) hre
      simpa using this
  · intro r r' h
    simpa using anti r r' h

end SublinearChoresMMS.Disposal.Dev.LA2.PartS
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part S: order statistics and the Borsuk–Ulam step (Step 1 of the proof of Lemma A.2) -/
alias ostat_sorted := SublinearChoresMMS.Disposal.Dev.LA2.PartS.ostat_sorted

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.LA2
open Finset Filter Topology
lemma ostat_neg {B k : ℕ} (D : Fin B → ℝ) (hk1 : 1 ≤ k) (hk2 : k ≤ B) :
    ostat k (fun v => -D v) = -ostat (B + 1 - k) D := by
  obtain ⟨rk, h1, h2⟩ := ostat_sorted D
  set r : Fin B := ⟨B - k, by omega⟩ with hr
  have e1 : ostat (B + 1 - k) D = D (rk.symm r) := by
    rw [h1 r]; congr 1; simp [hr]; omega
  rw [e1]
  refine ostat_eq_of _ _ ((Ici r).map rk.symm.toEmbedding) ?_ ?_ ?_
  · rw [card_map, Fin.card_Ici]; simp [hr]; omega
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_map.1 hv
    have := h2 r i (mem_Ici.1 hi)
    simp only [Equiv.coe_toEmbedding]
    linarith
  · intro S hS
    have hlt : (Ioi r).card < (S.map rk.toEmbedding).card := by
      rw [card_map, Fin.card_Ioi, hS]; simp [hr]; omega
    obtain ⟨e, he, hne⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨v, hv, rfl⟩ := mem_map.1 he
    refine ⟨v, hv, ?_⟩
    have hre : rk v ≤ r := by
      simpa [mem_Ioi, not_lt] using hne
    have := h2 (rk v) r hre
    simp only [Equiv.symm_apply_apply] at this
    linarith

lemma cont_iSup {ι X : Type*} [Fintype ι] [TopologicalSpace X] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp only [Real.iSup_of_isEmpty]; exact continuous_const
  · have : (fun x => ⨆ i, f i x) = fun x => univ.sup' univ_nonempty (fun i => f i x) :=
      funext fun x => (sup'_univ_eq_ciSup _).symm
    rw [this]
    exact Continuous.finset_sup'_apply _ fun i _ => hf i

lemma cont_iInf {ι X : Type*} [Fintype ι] [TopologicalSpace X] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨅ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp only [Real.iInf_of_isEmpty]; exact continuous_const
  · have : (fun x => ⨅ i, f i x) = fun x => univ.inf' univ_nonempty (fun i => f i x) :=
      funext fun x => (inf'_univ_eq_ciInf _).symm
    rw [this]
    exact Continuous.finset_inf'_apply _ fun i _ => hf i

lemma ostat_continuous {B : ℕ} (k : ℕ) : Continuous fun D : Fin B → ℝ => ostat k D := by
  unfold ostat
  exact cont_iSup _ fun S => cont_iInf _ fun v => continuous_apply _

/-- The clamp to `[-1, 1]`. -/
def cl (y : ℝ) : ℝ := max (-1) (min 1 y)

lemma cl_neg (y : ℝ) : cl (-y) = -cl y := by
  unfold cl
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma cl_mem (y : ℝ) : -1 ≤ cl y ∧ cl y ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma cl_of_ge {y : ℝ} (h : 1 ≤ y) : cl y = 1 := by
  unfold cl; rw [min_eq_left h]; norm_num

lemma cl_of_le {y : ℝ} (h : y ≤ -1) : cl y = -1 := by
  unfold cl; rw [min_eq_right (by linarith)]; exact max_eq_left h

lemma polyEval_neg {d : ℕ} (z : Fin (d + 1) → ℝ) (x : ℝ) :
    polyEval (-z) x = -polyEval z x := by
  simp [polyEval, Finset.sum_neg_distrib, neg_mul]

lemma polyEval_cont {d : ℕ} (x : ℝ) : Continuous fun z : Fin (d + 1) → ℝ => polyEval z x := by
  unfold polyEval
  exact continuous_finsetSum _ fun a _ => (continuous_apply a).mul continuous_const

/-- Step 1: a nonzero polynomial of degree ≤ d whose sign pattern balances `d` pairs of order
statistics of the bin differences `D_v(α) = Σ_t A v t α_t`. -/
theorem step1 {T B d : ℕ} (A : Fin B → Fin T → ℝ) (k : Fin d → ℕ)
    (hk : ∀ a, 1 ≤ k a ∧ k a ≤ B) :
    ∃ z : Fin (d + 1) → ℝ, z ≠ 0 ∧ ∃ α : Fin T → ℝ, (∀ t, -1 ≤ α t ∧ α t ≤ 1) ∧
      (∀ t : Fin T, polyEval z (t.val : ℝ) ≠ 0 → α t = Real.sign (polyEval z (t.val : ℝ))) ∧
      ∀ a, ostat (k a) (fun v => ∑ t, A v t * α t) +
        ostat (B + 1 - k a) (fun v => ∑ t, A v t * α t) = 0 := by
  let Df : (Fin T → ℝ) → Fin B → ℝ := fun α v => ∑ t, A v t * α t
  let g : (Fin T → ℝ) → Fin d → ℝ := fun α a =>
    ostat (k a) (fun v => ∑ t, A v t * α t) + ostat (B + 1 - k a) (fun v => ∑ t, A v t * α t)
  have hDc : Continuous Df :=
    continuous_pi fun v => continuous_finsetSum _ fun t _ =>
      continuous_const.mul (continuous_apply t)
  have hgc : Continuous g :=
    continuous_pi fun a => ((ostat_continuous _).comp hDc).add ((ostat_continuous _).comp hDc)
  have hg_odd : ∀ α, g (-α) = -g α := by
    intro α
    funext a
    have hD : (fun v => ∑ t, A v t * -α t) = fun v => -(∑ t, A v t * α t) := by
      funext v; simp [Finset.sum_neg_distrib]
    simp only [g, Pi.neg_apply]
    rw [hD, ostat_neg _ (hk a).1 (hk a).2,
      ostat_neg _ (by have := hk a; omega) (by have := hk a; omega)]
    have : B + 1 - (B + 1 - k a) = k a := by have := hk a; omega
    rw [this]; ring
  let αs : ℕ → (Fin (d + 1) → ℝ) → Fin T → ℝ := fun n z t =>
    cl (polyEval z (t.val : ℝ) * ((n : ℝ) + 1))
  have hαc : ∀ n, Continuous (αs n) := by
    intro n
    refine continuous_pi fun t => ?_
    have hcl : Continuous cl := by unfold cl; fun_prop
    exact hcl.comp ((polyEval_cont _).mul continuous_const)
  have hα_odd : ∀ n z, αs n (-z) = -αs n z := by
    intro n z; funext t
    simp only [αs, Pi.neg_apply, polyEval_neg, neg_mul, cl_neg]
  have hex : ∀ n : ℕ, ∃ z : EuclideanSpace ℝ (Fin (d + 1)), ‖z‖ = 1 ∧
      g (αs n (WithLp.ofLp z)) = 0 := by
    intro n
    let F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
        EuclideanSpace ℝ (Fin d)) :=
      ⟨fun x => WithLp.toLp 2 (g (αs n (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))))),
        (PiLp.continuous_toLp 2 _).comp (hgc.comp ((hαc n).comp
          ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)))⟩
    obtain ⟨x, hx⟩ := BorsukUlam.exists_eq_neg d F
    refine ⟨x, by simp, ?_⟩
    have h2 : g (αs n (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))) =
        g (αs n (WithLp.ofLp ((-x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
          EuclideanSpace ℝ (Fin (d + 1))))) :=
      WithLp.toLp_injective 2 hx
    rw [coe_neg_sphere, WithLp.ofLp_neg, hα_odd, hg_odd] at h2
    have := congrArg (fun y => y + g (αs n (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))))
      h2
    simp only [neg_add_cancel] at this
    have h3 : (2 : ℝ) • g (αs n (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))) = 0 := by
      rw [two_smul]; exact this
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  choose zs hzs hzg using hex
  let u : ℕ → EuclideanSpace ℝ (Fin (d + 1)) × (Fin T → ℝ) :=
    fun n => (zs n, αs n (WithLp.ofLp (zs n)))
  have hK : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 ×ˢ
      Set.Icc (-1 : Fin T → ℝ) 1) := (isCompact_sphere _ _).prod isCompact_Icc
  have hmem : ∀ n, u n ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 ×ˢ
      Set.Icc (-1 : Fin T → ℝ) 1 := by
    intro n
    refine ⟨by simpa using hzs n, fun t => (cl_mem _).1, fun t => (cl_mem _).2⟩
  obtain ⟨⟨z, α⟩, ⟨hz, hα⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hlimz : Tendsto (fun n => zs (φ n)) atTop (𝓝 z) := (continuous_fst.tendsto _).comp hlim
  have hlimα : Tendsto (fun n => αs (φ n) (WithLp.ofLp (zs (φ n)))) atTop (𝓝 α) :=
    (continuous_snd.tendsto _).comp hlim
  refine ⟨WithLp.ofLp z, ?_, α, fun t => ⟨hα.1 t, hα.2 t⟩, ?_, ?_⟩
  · intro h
    rw [WithLp.ofLp_eq_zero] at h
    have : ‖z‖ = 1 := by simpa using hz
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · intro t hne
    set c := polyEval (WithLp.ofLp z) (t.val : ℝ) with hc
    have hpc : Tendsto (fun n => polyEval (WithLp.ofLp (zs (φ n))) (t.val : ℝ)) atTop (𝓝 c) :=
      (((polyEval_cont _).comp (PiLp.continuous_ofLp 2 _)).tendsto z).comp hlimz
    have hαt : Tendsto (fun n => αs (φ n) (WithLp.ofLp (zs (φ n))) t) atTop (𝓝 (α t)) :=
      ((continuous_apply t).tendsto α).comp hlimα
    have hφn : ∀ n : ℕ, (n : ℝ) ≤ (φ n : ℝ) := fun n => by exact_mod_cast hφ.id_le n
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have ev1 : ∀ᶠ n in atTop, polyEval (WithLp.ofLp (zs (φ n))) (t.val : ℝ) < c / 2 :=
        hpc.eventually (gt_mem_nhds (by linarith))
      have ev2 : ∀ᶠ n : ℕ in atTop, ⌈-2 / c⌉₊ ≤ n := eventually_ge_atTop _
      have ev : ∀ᶠ n in atTop, αs (φ n) (WithLp.ofLp (zs (φ n))) t = -1 := by
        filter_upwards [ev1, ev2] with n h1 h2
        apply cl_of_le
        have hm : -2 / c ≤ (φ n : ℝ) + 1 := by
          have := Nat.le_ceil (-2 / c)
          have h2' : ((⌈-2 / c⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
          linarith [hφn n]
        have hpos1 : (0 : ℝ) < (φ n : ℝ) + 1 := by positivity
        calc polyEval (WithLp.ofLp (zs (φ n))) (t.val : ℝ) * ((φ n : ℝ) + 1)
            ≤ c / 2 * ((φ n : ℝ) + 1) := by nlinarith
          _ ≤ c / 2 * (-2 / c) := by
            exact mul_le_mul_of_nonpos_left hm (by linarith)
          _ = -1 := by field_simp
      have := tendsto_nhds_unique hαt (tendsto_const_nhds.congr' (ev.mono fun n h => h.symm))
      rw [this, Real.sign_of_neg hneg]
    · have ev1 : ∀ᶠ n in atTop, c / 2 < polyEval (WithLp.ofLp (zs (φ n))) (t.val : ℝ) :=
        hpc.eventually (lt_mem_nhds (by linarith))
      have ev2 : ∀ᶠ n : ℕ in atTop, ⌈2 / c⌉₊ ≤ n := eventually_ge_atTop _
      have ev : ∀ᶠ n in atTop, αs (φ n) (WithLp.ofLp (zs (φ n))) t = 1 := by
        filter_upwards [ev1, ev2] with n h1 h2
        apply cl_of_ge
        have hm : 2 / c ≤ (φ n : ℝ) + 1 := by
          have := Nat.le_ceil (2 / c)
          have h2' : ((⌈2 / c⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
          linarith [hφn n]
        have hpos1 : (0 : ℝ) < (φ n : ℝ) + 1 := by positivity
        calc (1 : ℝ) = c / 2 * (2 / c) := by field_simp
          _ ≤ c / 2 * ((φ n : ℝ) + 1) := mul_le_mul_of_nonneg_left hm (by linarith)
          _ ≤ polyEval (WithLp.ofLp (zs (φ n))) (t.val : ℝ) * ((φ n : ℝ) + 1) := by nlinarith
      have := tendsto_nhds_unique hαt (tendsto_const_nhds.congr' (ev.mono fun n h => h.symm))
      rw [this, Real.sign_of_pos hpos]
  · have hgα : g α = 0 := by
      have h1 : Tendsto (fun n => g (αs (φ n) (WithLp.ofLp (zs (φ n))))) atTop (𝓝 (g α)) :=
        (hgc.tendsto α).comp hlimα
      have h2 : (fun n => g (αs (φ n) (WithLp.ofLp (zs (φ n))))) = fun _ => 0 :=
        funext fun n => hzg (φ n)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    intro a
    exact congrFun hgα a

end SublinearChoresMMS.Disposal.Dev.LA2.PartS
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
alias step1 := SublinearChoresMMS.Disposal.Dev.LA2.PartS.step1

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartG
open Finset
set_option linter.unusedSectionVars false
variable {σ : Type} [DecidableEq σ]
/-- Reachability along chore-edges and local-edges. -/
def Reach (ce L : σ → σ) (y t : σ) : Prop :=
  Relation.ReflTransGen (fun a b => b = ce a ∨ b = L a) y t

lemma reach_ce {ce L : σ → σ} {y t : σ} (h : Reach ce L y t) : Reach ce L y (ce t) :=
  Relation.ReflTransGen.tail h (Or.inl rfl)

lemma reach_L {ce L : σ → σ} {y t : σ} (h : Reach ce L y t) : Reach ce L y (L t) :=
  Relation.ReflTransGen.tail h (Or.inr rfl)

lemma reach_refl (ce L : σ → σ) (y : σ) : Reach ce L y y := Relation.ReflTransGen.refl

lemma reach_closed {ce L : σ → σ} {y t : σ} (T : σ → Prop) (h0 : T y)
    (hc : ∀ a, T a → T (ce a) ∧ T (L a)) (h : Reach ce L y t) : T t := by
  induction h with
  | refl => exact h0
  | tail _ hab ih =>
    rcases hab with rfl | rfl
    · exact (hc _ ih).1
    · exact (hc _ ih).2

lemma reach_mono {ce L L' : σ → σ} {y w u : σ} (hL : ∀ a, L' a = a ∨ L' a = L a)
    (hw : Reach ce L y w) (h : Reach ce L' w u) : Reach ce L y u := by
  induction h with
  | refl => exact hw
  | tail _ hab ih =>
    rcases hab with rfl | rfl
    · exact reach_ce ih
    · rcases hL _ with h | h
      · rw [h]; exact ih
      · rw [h]; exact reach_L ih

/-- Cutting the local-edges inside `A`. -/
def cut (L : σ → σ) (A : Finset σ) (t : σ) : σ := if t ∈ A then t else L t

lemma cut_invol {L : σ → σ} (hL : Function.Involutive L) {A : Finset σ}
    (hA : ∀ a ∈ A, L a ∈ A) : Function.Involutive (cut L A) := by
  intro t
  unfold cut
  by_cases ht : t ∈ A
  · simp [ht]
  · have : L t ∉ A := fun h => ht (by simpa [hL t] using hA _ h)
    simp [ht, this, hL t]

lemma cut_cases (L : σ → σ) (A : Finset σ) (a : σ) : cut L A a = a ∨ cut L A a = L a := by
  unfold cut; split_ifs <;> simp

lemma cut_of_not_mem {L : σ → σ} {A : Finset σ} {a : σ} (h : a ∉ A) : cut L A a = L a := by
  simp [cut, h]

lemma cut_of_mem {L : σ → σ} {A : Finset σ} {a : σ} (h : a ∈ A) : cut L A a = a := by
  simp [cut, h]

structure Good (ce L : σ → σ) (S : Finset σ) (base : ℕ) (col : σ → Bool) (lab : σ → ℕ) :
    Prop where
  c1 : ∀ s ∈ S, col (ce s) ≠ col s
  c2 : ∀ s ∈ S, L s ≠ s → col (L s) ≠ col s
  c3 : ∀ s ∈ S, lab (ce s) = lab s
  c4 : ∀ s ∈ S, ∀ s' ∈ S, lab s = lab s' → s' = s ∨ s' = ce s
  c5 : ∀ s ∈ S, base ≤ lab s ∧ 2 * lab s < 2 * base + S.card
  c6 : ∀ s ∈ S, ∀ s' ∈ S, L s ≠ s → L s' ≠ s' → lab s + 2 ≤ lab (L s) →
    lab s' + 2 ≤ lab (L s') → s' = s ∨ lab (L s') < lab s ∨ lab (L s) < lab s'

structure Anch (ce L : σ → σ) (S : Finset σ) (base : ℕ) (col : σ → Bool) (lab : σ → ℕ)
    (y : σ) : Prop where
  a1 : lab y = base
  a2 : ∀ t ∈ S, ∀ u ∈ S, Reach ce L y t → ¬ Reach ce L y u → lab t < lab u
  a3 : ∃ t ∈ S, t ≠ y ∧ Reach ce L y t ∧ L t = t ∧ col t ≠ col y
  a4 : ∀ s ∈ S, Reach ce L y s → L s ≠ s → lab (L s) ≤ lab s + 1

def extCol (x z : σ) (c : Bool) (col' : σ → Bool) (s : σ) : Bool :=
  if s = x then c else if s = z then !c else col' s

def extLab (x z : σ) (base : ℕ) (lab' : σ → ℕ) (s : σ) : ℕ :=
  if s = x ∨ s = z then base else lab' s

lemma extCol_x (x z : σ) (c : Bool) (col' : σ → Bool) : extCol x z c col' x = c := by
  simp [extCol]

lemma extCol_z {x z : σ} (h : z ≠ x) (c : Bool) (col' : σ → Bool) :
    extCol x z c col' z = !c := by
  simp [extCol, h]

lemma extCol_o {x z s : σ} (hx : s ≠ x) (hz : s ≠ z) (c : Bool) (col' : σ → Bool) :
    extCol x z c col' s = col' s := by
  simp [extCol, hx, hz]

lemma extLab_x (x z : σ) (b : ℕ) (lab' : σ → ℕ) : extLab x z b lab' x = b := by
  simp [extLab]

lemma extLab_z (x z : σ) (b : ℕ) (lab' : σ → ℕ) : extLab x z b lab' z = b := by
  simp [extLab]

lemma extLab_o {x z s : σ} (hx : s ≠ x) (hz : s ≠ z) (b : ℕ) (lab' : σ → ℕ) :
    extLab x z b lab' s = lab' s := by
  simp [extLab, hx, hz]

lemma mem_S' {S : Finset σ} {x z s : σ} : s ∈ (S.erase x).erase z ↔ s ≠ z ∧ s ≠ x ∧ s ∈ S := by
  simp [mem_erase]

lemma card_S' {S : Finset σ} {x z : σ} (hx : x ∈ S) (hz : z ∈ S) (hzx : z ≠ x) :
    ((S.erase x).erase z).card + 2 = S.card := by
  have h1 : z ∈ S.erase x := mem_erase.2 ⟨hzx, hz⟩
  rw [card_erase_of_mem h1, card_erase_of_mem hx]
  have : 2 ≤ S.card := by
    have : ({x, z} : Finset σ) ⊆ S := by
      intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption
    have h2 := card_le_card this
    rw [card_pair hzx.symm] at h2
    exact h2
  omega

/-- The parts of `Good` not involving the local-edges, for the extension by the chore-edge
`{x, z}`. -/
lemma basic {ce L' : σ → σ} (hce : Function.Involutive ce) (hce0 : ∀ s, ce s ≠ s)
    {S : Finset σ} (hSc : ∀ s ∈ S, ce s ∈ S) {x z : σ} (hx : x ∈ S) (hz : ce x = z)
    {base : ℕ} {c : Bool} {col' : σ → Bool} {lab' : σ → ℕ}
    (hG : Good ce L' ((S.erase x).erase z) (base + 1) col' lab') :
    (∀ s ∈ S, extCol x z c col' (ce s) ≠ extCol x z c col' s) ∧
    (∀ s ∈ S, extLab x z base lab' (ce s) = extLab x z base lab' s) ∧
    (∀ s ∈ S, ∀ s' ∈ S, extLab x z base lab' s = extLab x z base lab' s' →
      s' = s ∨ s' = ce s) ∧
    (∀ s ∈ S, base ≤ extLab x z base lab' s ∧
      2 * extLab x z base lab' s < 2 * base + S.card) := by
  have hzx : z ≠ x := by rw [← hz]; exact hce0 x
  have hzS : z ∈ S := hz ▸ hSc x hx
  have hcz : ce z = x := by rw [← hz]; exact hce x
  have hcard := card_S' hx hzS hzx
  -- for s ∉ {x, z}, ce s ∉ {x, z}
  have hcs : ∀ s, s ≠ x → s ≠ z → ce s ≠ x ∧ ce s ≠ z := by
    intro s h1 h2
    constructor
    · intro h; apply h2; rw [← hz, ← h, hce s]
    · intro h; apply h1; rw [← hcz, ← h, hce s]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    by_cases h1 : s = x
    · subst h1; rw [hz, extCol_z hzx, extCol_x]; simp
    by_cases h2 : s = z
    · subst h2; rw [hcz, extCol_z hzx, extCol_x]; simp
    obtain ⟨h3, h4⟩ := hcs s h1 h2
    rw [extCol_o h3 h4, extCol_o h1 h2]
    exact hG.c1 s (mem_S'.2 ⟨h2, h1, hs⟩)
  · intro s hs
    by_cases h1 : s = x
    · subst h1; rw [hz, extLab_z, extLab_x]
    by_cases h2 : s = z
    · subst h2; rw [hcz, extLab_z, extLab_x]
    obtain ⟨h3, h4⟩ := hcs s h1 h2
    rw [extLab_o h3 h4, extLab_o h1 h2]
    exact hG.c3 s (mem_S'.2 ⟨h2, h1, hs⟩)
  · intro s hs s' hs' he
    have key : ∀ t ∈ S, t ≠ x → t ≠ z → base + 1 ≤ extLab x z base lab' t := by
      intro t ht h1 h2
      rw [extLab_o h1 h2]
      exact (hG.c5 t (mem_S'.2 ⟨h2, h1, ht⟩)).1
    by_cases h1 : s = x
    · subst h1
      rw [extLab_x] at he
      by_cases h1' : s' = s
      · exact Or.inl h1'
      by_cases h2' : s' = z
      · exact Or.inr (h2'.trans hz.symm)
      have := key s' hs' h1' h2'; omega
    by_cases h2 : s = z
    · subst h2
      rw [extLab_z] at he
      by_cases h1' : s' = x
      · exact Or.inr (h1'.trans hcz.symm)
      by_cases h2' : s' = s
      · exact Or.inl h2'
      have := key s' hs' h1' h2'; omega
    have := key s hs h1 h2
    by_cases h1' : s' = x
    · subst h1'; rw [extLab_x] at he; omega
    by_cases h2' : s' = z
    · subst h2'; rw [extLab_z] at he; omega
    rw [extLab_o h1 h2, extLab_o h1' h2'] at he
    exact hG.c4 s (mem_S'.2 ⟨h2, h1, hs⟩) s' (mem_S'.2 ⟨h2', h1', hs'⟩) he
  · intro s hs
    by_cases h1 : s = x
    · subst h1; rw [extLab_x]; omega
    by_cases h2 : s = z
    · subst h2; rw [extLab_z]; omega
    rw [extLab_o h1 h2]
    have := hG.c5 s (mem_S'.2 ⟨h2, h1, hs⟩)
    omega

lemma S'_closed_ce {ce : σ → σ} (hce : Function.Involutive ce)
    {S : Finset σ} (hSc : ∀ s ∈ S, ce s ∈ S) {x z : σ} (hz : ce x = z) :
    ∀ s ∈ (S.erase x).erase z, ce s ∈ (S.erase x).erase z := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := mem_S'.1 hs
  refine mem_S'.2 ⟨?_, ?_, hSc s h3⟩
  · intro h; apply h2; rw [← hz] at h; exact hce.injective h
  · intro h; apply h1; rw [← hz, ← h, hce s]

/-- The induction hypothesis. -/
def IHyp (ce : σ → σ) (n : ℕ) : Prop :=
  ∀ (S : Finset σ) (L : σ → σ) (base : ℕ), S.card < n → Function.Involutive L →
    (∀ s ∈ S, ce s ∈ S) → (∀ s ∈ S, L s ∈ S) →
    (∃ col lab, Good ce L S base col lab) ∧
    (∀ y ∈ S, L y = y → ∃ col lab, Good ce L S base col lab ∧ Anch ce L S base col lab y)

/-- A component that is a path, processed from its end `x`. -/
lemma path_case {ce L : σ → σ} (hce : Function.Involutive ce) (hce0 : ∀ s, ce s ≠ s)
    {S : Finset σ} (ih : IHyp ce S.card) (hL : Function.Involutive L)
    (hSc : ∀ s ∈ S, ce s ∈ S) (hSL : ∀ s ∈ S, L s ∈ S) (base : ℕ)
    {x : σ} (hx : x ∈ S) (hLx : L x = x) :
    ∃ col lab, Good ce L S base col lab ∧ Anch ce L S base col lab x := by
  obtain ⟨z, hz⟩ : ∃ z, ce x = z := ⟨_, rfl⟩
  have hzx : z ≠ x := by rw [← hz]; exact hce0 x
  have hzS : z ∈ S := hz ▸ hSc x hx
  have hcz : ce z = x := by rw [← hz]; exact hce x
  have hcard := card_S' hx hzS hzx
  obtain ⟨S', hS'⟩ : ∃ S', S' = (S.erase x).erase z := ⟨_, rfl⟩
  rw [← hS'] at hcard
  have memS' : ∀ s, s ∈ S' ↔ s ≠ z ∧ s ≠ x ∧ s ∈ S := fun s => by rw [hS']; exact mem_S'
  have hS'c : ∀ s ∈ S', ce s ∈ S' := by rw [hS']; exact S'_closed_ce hce hSc hz
  have hxz : Reach ce L x z := by
    have := reach_ce (reach_refl ce L x); rwa [hz] at this
  by_cases hLz : L z = z
  · -- a single chore-edge component
    have hS'L : ∀ s ∈ S', L s ∈ S' := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := (memS' s).1 hs
      refine (memS' _).2 ⟨?_, ?_, hSL s h3⟩
      · intro h; apply h1; rw [← hLz, ← h, hL s]
      · intro h; apply h2; rw [← hLx, ← h, hL s]
    obtain ⟨col', lab', hG⟩ := (ih S' L (base + 1) (by omega) hL hS'c hS'L).1
    have hG0 := hG; rw [hS'] at hG0
    obtain ⟨b1, b3, b4, b5⟩ := basic hce hce0 hSc hx hz (c := true) hG0
    have hRx : ∀ a, Reach ce L x a → a = x ∨ a = z := by
      intro a h
      refine reach_closed (fun a => a = x ∨ a = z) (Or.inl rfl) ?_ h
      rintro b (rfl | rfl)
      · exact ⟨Or.inr hz, Or.inl hLx⟩
      · exact ⟨Or.inl hcz, Or.inr hLz⟩
    refine ⟨extCol x z true col', extLab x z base lab', ⟨b1, ?_, b3, b4, b5, ?_⟩, ?_⟩
    · intro s hs hne
      have h1 : s ≠ x := by rintro rfl; exact hne hLx
      have h2 : s ≠ z := by rintro rfl; exact hne hLz
      have hs' : s ∈ S' := (memS' s).2 ⟨h2, h1, hs⟩
      obtain ⟨h3, h4, -⟩ := (memS' _).1 (hS'L s hs')
      rw [extCol_o h4 h3, extCol_o h1 h2]
      exact hG.c2 s hs' hne
    · intro s hs s' hs' hne hne' hl hl'
      have h1 : s ≠ x := by rintro rfl; exact hne hLx
      have h2 : s ≠ z := by rintro rfl; exact hne hLz
      have h1' : s' ≠ x := by rintro rfl; exact hne' hLx
      have h2' : s' ≠ z := by rintro rfl; exact hne' hLz
      have hsS : s ∈ S' := (memS' s).2 ⟨h2, h1, hs⟩
      have hsS' : s' ∈ S' := (memS' s').2 ⟨h2', h1', hs'⟩
      obtain ⟨h3, h4, -⟩ := (memS' _).1 (hS'L s hsS)
      obtain ⟨h3', h4', -⟩ := (memS' _).1 (hS'L s' hsS')
      rw [extLab_o h4 h3, extLab_o h1 h2] at hl
      rw [extLab_o h4' h3', extLab_o h1' h2'] at hl'
      rw [extLab_o h4 h3, extLab_o h1 h2, extLab_o h4' h3', extLab_o h1' h2']
      exact hG.c6 s hsS s' hsS' hne hne' hl hl'
    · refine ⟨extLab_x _ _ _ _, ?_, ?_, ?_⟩
      · intro t ht u hu hrt hru
        have hux : u ≠ x := fun h => hru (h ▸ reach_refl ce L x)
        have huz : u ≠ z := fun h => hru (h ▸ hxz)
        have huS : u ∈ S' := (memS' u).2 ⟨huz, hux, hu⟩
        have := (hG.c5 u huS).1
        rw [extLab_o hux huz]
        rcases hRx t hrt with rfl | rfl
        · rw [extLab_x]; omega
        · rw [extLab_z]; omega
      · refine ⟨z, hzS, hzx, hxz, hLz, ?_⟩
        rw [extCol_z hzx, extCol_x]; simp
      · intro s hs hrs hne
        rcases hRx s hrs with rfl | rfl
        · exact absurd hLx hne
        · exact absurd hLz hne
  · -- the path continues: z — w
    obtain ⟨w, hw⟩ : ∃ w, L z = w := ⟨_, rfl⟩
    have hLw : L w = z := by rw [← hw]; exact hL z
    have hwx : w ≠ x := by
      intro h; apply hzx; rw [← hLw, h, hLx]
    have hwz : w ≠ z := fun h => hLz (hw.trans h)
    have hwS : w ∈ S := hw ▸ hSL z hzS
    obtain ⟨A, hAdef⟩ : ∃ A : Finset σ, A = {x, z, w} := ⟨_, rfl⟩
    have hmemA : ∀ a, a ∈ A ↔ a = x ∨ a = z ∨ a = w := by intro a; simp [hAdef]
    have hA : ∀ a ∈ A, L a ∈ A := by
      intro a ha
      rw [hmemA] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · exact Or.inl hLx
      · exact Or.inr (Or.inr hw)
      · exact Or.inr (Or.inl hLw)
    have hS'L : ∀ s ∈ S', cut L A s ∈ S' := by
      intro s hs
      by_cases hsA : s ∈ A
      · rw [cut_of_mem hsA]; exact hs
      · rw [cut_of_not_mem hsA]
        obtain ⟨h1, h2, h3⟩ := (memS' s).1 hs
        refine (memS' _).2 ⟨?_, ?_, hSL s h3⟩
        · intro h; apply hsA; rw [hmemA]; right; right; rw [← hw, ← h, hL s]
        · intro h; apply h2; rw [← hLx, ← h, hL s]
    have hwS' : w ∈ S' := (memS' w).2 ⟨hwz, hwx, hwS⟩
    have hL'w : cut L A w = w := cut_of_mem ((hmemA w).2 (Or.inr (Or.inr rfl)))
    obtain ⟨col', lab', hG, hAn⟩ :=
      (ih S' (cut L A) (base + 1) (by omega) (cut_invol hL hA) hS'c hS'L).2 w hwS' hL'w
    have hG0 := hG; rw [hS'] at hG0
    obtain ⟨b1, b3, b4, b5⟩ := basic hce hce0 hSc hx hz (c := col' w) hG0
    have hcolw : extCol x z (col' w) col' w = col' w := extCol_o hwx hwz _ _
    have hlabw : extLab x z base lab' w = base + 1 := by rw [extLab_o hwx hwz, hAn.a1]
    have hgen : ∀ s ∈ S, s ≠ x → s ≠ z → s ≠ w →
        s ∈ S' ∧ cut L A s = L s ∧ L s ∈ S' ∧ L s ≠ x ∧ L s ≠ z := by
      intro s hs h1 h2 h3
      have hs' : s ∈ S' := (memS' s).2 ⟨h2, h1, hs⟩
      have hsA : s ∉ A := by rw [hmemA]; tauto
      have hc := cut_of_not_mem (L := L) hsA
      have hL' := hS'L s hs'
      rw [hc] at hL'
      obtain ⟨h4, h5, -⟩ := (memS' _).1 hL'
      exact ⟨hs', hc, hL', h5, h4⟩
    have hR' : ∀ a, Reach ce (cut L A) w a → a ∈ S' := fun a h =>
      reach_closed (· ∈ S') hwS' (fun b hb => ⟨hS'c b hb, hS'L b hb⟩) h
    have hxw : Reach ce L x w := by
      have := reach_L hxz; rwa [hw] at this
    have hback : ∀ a, Reach ce (cut L A) w a → Reach ce L x a := fun a h =>
      reach_mono (cut_cases L A) hxw h
    have hfwd : ∀ a, Reach ce L x a → a = x ∨ a = z ∨ Reach ce (cut L A) w a := by
      intro a h
      refine reach_closed (fun a => a = x ∨ a = z ∨ Reach ce (cut L A) w a) (Or.inl rfl) ?_ h
      rintro b (rfl | rfl | hb)
      · exact ⟨Or.inr (Or.inl hz), Or.inl hLx⟩
      · exact ⟨Or.inl hcz, Or.inr (Or.inr (hw ▸ reach_refl _ _ _))⟩
      · refine ⟨Or.inr (Or.inr (reach_ce hb)), ?_⟩
        by_cases hbA : b ∈ A
        · have hbS := (memS' b).1 (hR' b hb)
          rw [hmemA] at hbA
          rcases hbA with h | h | h
          · exact absurd h hbS.2.1
          · exact absurd h hbS.1
          · rw [h, hLw]; exact Or.inr (Or.inl rfl)
        · have := reach_L hb; rw [cut_of_not_mem hbA] at this; exact Or.inr (Or.inr this)
    refine ⟨extCol x z (col' w) col', extLab x z base lab', ⟨b1, ?_, b3, b4, b5, ?_⟩, ?_⟩
    · intro s hs hne
      by_cases h1 : s = x
      · rw [h1] at hne; exact absurd hLx hne
      by_cases h2 : s = z
      · rw [h2, hw, hcolw, extCol_z hzx]; simp
      by_cases h3 : s = w
      · rw [h3, hLw, hcolw, extCol_z hzx]; simp
      obtain ⟨hs', hc, -, hLx', hLz'⟩ := hgen s hs h1 h2 h3
      rw [extCol_o hLx' hLz', extCol_o h1 h2]
      have := hG.c2 s hs' (by rw [hc]; exact hne)
      rwa [hc] at this
    · have hlong : ∀ s ∈ S, L s ≠ s → extLab x z base lab' s + 2 ≤ extLab x z base lab' (L s) →
          s ∈ S' ∧ cut L A s = L s ∧ extLab x z base lab' s = lab' s ∧
          extLab x z base lab' (L s) = lab' (cut L A s) := by
        intro s hs hne hl
        by_cases h1 : s = x
        · rw [h1] at hne; exact absurd hLx hne
        by_cases h2 : s = z
        · rw [h2, hw, hlabw, extLab_z] at hl; omega
        by_cases h3 : s = w
        · rw [h3, hLw, hlabw, extLab_z] at hl; omega
        obtain ⟨hs', hc, -, hLx', hLz'⟩ := hgen s hs h1 h2 h3
        exact ⟨hs', hc, extLab_o h1 h2 _ _, by rw [hc, extLab_o hLx' hLz']⟩
      intro s hs s' hs' hne hne' hl hl'
      obtain ⟨hsS, hc, e1, e2⟩ := hlong s hs hne hl
      obtain ⟨hsS', hc', e1', e2'⟩ := hlong s' hs' hne' hl'
      rw [e1, e2] at hl
      rw [e1', e2'] at hl'
      rw [e1, e2, e1', e2']
      have := hG.c6 s hsS s' hsS' (by rw [hc]; exact hne) (by rw [hc']; exact hne') hl hl'
      rwa [hc, hc'] at this ⊢
    · refine ⟨extLab_x _ _ _ _, ?_, ?_, ?_⟩
      · intro t ht u hu hrt hru
        have hux : u ≠ x := fun h => hru (h ▸ reach_refl ce L x)
        have huz : u ≠ z := fun h => hru (h ▸ hxz)
        have huS : u ∈ S' := (memS' u).2 ⟨huz, hux, hu⟩
        have hu' : ¬ Reach ce (cut L A) w u := fun h => hru (hback u h)
        have := (hG.c5 u huS).1
        rw [extLab_o hux huz]
        rcases hfwd t hrt with rfl | rfl | ht'
        · rw [extLab_x]; omega
        · rw [extLab_z]; omega
        · have htS := (memS' t).1 (hR' t ht')
          rw [extLab_o htS.2.1 htS.1]
          exact hAn.a2 t (hR' t ht') u huS ht' hu'
      · obtain ⟨t, htS', htw, hrt, hLt, hct⟩ := hAn.a3
        have htS := (memS' t).1 htS'
        have htA : t ∉ A := by rw [hmemA]; have := htS.1; have := htS.2.1; tauto
        rw [cut_of_not_mem htA] at hLt
        refine ⟨t, htS.2.2, htS.2.1, hback t hrt, hLt, ?_⟩
        rw [extCol_o htS.2.1 htS.1, extCol_x]; exact hct
      · intro s hs hrs hne
        rcases hfwd s hrs with rfl | rfl | hs'
        · exact absurd hLx hne
        · rw [hw, hlabw, extLab_z]
        · by_cases hsw : s = w
          · rw [hsw, hLw, hlabw, extLab_z]; omega
          have hsS := (memS' s).1 (hR' s hs')
          obtain ⟨hsS', hc, -, hLx', hLz'⟩ := hgen s hs hsS.2.1 hsS.1 hsw
          rw [extLab_o hLx' hLz', extLab_o hsS.2.1 hsS.1]
          have := hAn.a4 s hsS' hs' (by rw [hc]; exact hne)
          rwa [hc] at this

/-- No unmatched element left: the component of `x` is a cycle. -/
lemma cycle_case {ce L : σ → σ} (hce : Function.Involutive ce) (hce0 : ∀ s, ce s ≠ s)
    {S : Finset σ} (ih : IHyp ce S.card) (hL : Function.Involutive L)
    (hSc : ∀ s ∈ S, ce s ∈ S) (hSL : ∀ s ∈ S, L s ∈ S) (base : ℕ)
    {x : σ} (hx : x ∈ S) (hnf : ∀ s ∈ S, L s ≠ s) :
    ∃ col lab, Good ce L S base col lab := by
  obtain ⟨z, hz⟩ : ∃ z, ce x = z := ⟨_, rfl⟩
  have hzx : z ≠ x := by rw [← hz]; exact hce0 x
  have hzS : z ∈ S := hz ▸ hSc x hx
  have hcard := card_S' hx hzS hzx
  obtain ⟨S', hS'⟩ : ∃ S', S' = (S.erase x).erase z := ⟨_, rfl⟩
  rw [← hS'] at hcard
  have memS' : ∀ s, s ∈ S' ↔ s ≠ z ∧ s ≠ x ∧ s ∈ S := fun s => by rw [hS']; exact mem_S'
  have hS'c : ∀ s ∈ S', ce s ∈ S' := by rw [hS']; exact S'_closed_ce hce hSc hz
  obtain ⟨w, hw⟩ : ∃ w, L z = w := ⟨_, rfl⟩
  have hLw : L w = z := by rw [← hw]; exact hL z
  by_cases hwx : w = x
  · -- a 2-cycle
    rw [hwx] at hw hLw
    have hS'L : ∀ s ∈ S', L s ∈ S' := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := (memS' s).1 hs
      refine (memS' _).2 ⟨?_, ?_, hSL s h3⟩
      · intro h; apply h2; rw [← hw, ← h, hL s]
      · intro h; apply h1; rw [← hLw, ← h, hL s]
    obtain ⟨col', lab', hG⟩ := (ih S' L (base + 1) (by omega) hL hS'c hS'L).1
    have hG0 := hG; rw [hS'] at hG0
    obtain ⟨b1, b3, b4, b5⟩ := basic hce hce0 hSc hx hz (c := true) hG0
    have hred : ∀ s ∈ S, s ≠ x → s ≠ z → s ∈ S' ∧ L s ≠ x ∧ L s ≠ z := by
      intro s hs h1 h2
      have hs' : s ∈ S' := (memS' s).2 ⟨h2, h1, hs⟩
      obtain ⟨h3, h4, -⟩ := (memS' _).1 (hS'L s hs')
      exact ⟨hs', h4, h3⟩
    refine ⟨extCol x z true col', extLab x z base lab', b1, ?_, b3, b4, b5, ?_⟩
    · intro s hs hne
      by_cases h1 : s = x
      · rw [h1, hLw, extCol_z hzx, extCol_x]; simp
      by_cases h2 : s = z
      · rw [h2, hw, extCol_z hzx, extCol_x]; simp
      obtain ⟨hs', h3, h4⟩ := hred s hs h1 h2
      rw [extCol_o h3 h4, extCol_o h1 h2]
      exact hG.c2 s hs' hne
    · have hlong : ∀ s ∈ S, extLab x z base lab' s + 2 ≤ extLab x z base lab' (L s) →
          s ∈ S' ∧ extLab x z base lab' s = lab' s ∧
          extLab x z base lab' (L s) = lab' (L s) := by
        intro s hs hl
        by_cases h1 : s = x
        · rw [h1, hLw, extLab_z, extLab_x] at hl; omega
        by_cases h2 : s = z
        · rw [h2, hw, extLab_z, extLab_x] at hl; omega
        obtain ⟨hs', h3, h4⟩ := hred s hs h1 h2
        exact ⟨hs', extLab_o h1 h2 _ _, extLab_o h3 h4 _ _⟩
      intro s hs s' hs' hne hne' hl hl'
      obtain ⟨hsS, e1, e2⟩ := hlong s hs hl
      obtain ⟨hsS', e1', e2'⟩ := hlong s' hs' hl'
      rw [e1, e2] at hl
      rw [e1', e2'] at hl'
      rw [e1, e2, e1', e2']
      exact hG.c6 s hsS s' hsS' hne hne' hl hl'
  · -- a longer cycle: cut it open at the local-edges x — v and z — w
    obtain ⟨v, hv⟩ : ∃ v, L x = v := ⟨_, rfl⟩
    have hLv : L v = x := by rw [← hv]; exact hL x
    have hvx : v ≠ x := by rw [← hv]; exact hnf x hx
    have hwz : w ≠ z := by rw [← hw]; exact hnf z hzS
    have hvz : v ≠ z := by
      intro h; apply hwx; rw [← hw, ← h, hLv]
    have hvw : v ≠ w := by
      intro h; apply hzx; rw [← hLw, ← h, hLv]
    have hwS : w ∈ S := hw ▸ hSL z hzS
    have hvS : v ∈ S := hv ▸ hSL x hx
    obtain ⟨A, hAdef⟩ : ∃ A : Finset σ, A = {x, z, w, v} := ⟨_, rfl⟩
    have hmemA : ∀ a, a ∈ A ↔ a = x ∨ a = z ∨ a = w ∨ a = v := by intro a; simp [hAdef]
    have hA : ∀ a ∈ A, L a ∈ A := by
      intro a ha
      rw [hmemA] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr hv))
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inl hLw)
      · exact Or.inl hLv
    have hS'L : ∀ s ∈ S', cut L A s ∈ S' := by
      intro s hs
      by_cases hsA : s ∈ A
      · rw [cut_of_mem hsA]; exact hs
      · rw [cut_of_not_mem hsA]
        obtain ⟨h1, h2, h3⟩ := (memS' s).1 hs
        refine (memS' _).2 ⟨?_, ?_, hSL s h3⟩
        · intro h; apply hsA; rw [hmemA]; right; right; left; rw [← hw, ← h, hL s]
        · intro h; apply hsA; rw [hmemA]; right; right; right; rw [← hv, ← h, hL s]
    have hwS' : w ∈ S' := (memS' w).2 ⟨hwz, hwx, hwS⟩
    have hvS' : v ∈ S' := (memS' v).2 ⟨hvz, hvx, hvS⟩
    have hL'w : cut L A w = w := cut_of_mem ((hmemA w).2 (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨col', lab', hG, hAn⟩ :=
      (ih S' (cut L A) (base + 1) (by omega) (cut_invol hL hA) hS'c hS'L).2 w hwS' hL'w
    have hG0 := hG; rw [hS'] at hG0
    obtain ⟨b1, b3, b4, b5⟩ := basic hce hce0 hSc hx hz (c := col' w) hG0
    -- the other end of the opened cycle is `v`
    obtain ⟨hrv, hcv⟩ : Reach ce (cut L A) w v ∧ col' v ≠ col' w := by
      obtain ⟨t, htS', htw, hrt, hLt, hct⟩ := hAn.a3
      have htS := (memS' t).1 htS'
      have htA : t ∈ A := by
        by_contra hta
        rw [cut_of_not_mem hta] at hLt
        exact hnf t htS.2.2 hLt
      have htv : t = v := by
        rw [hmemA] at htA
        rcases htA with h | h | h | h
        · exact absurd h htS.2.1
        · exact absurd h htS.1
        · exact absurd h htw
        · exact h
      rw [htv] at hrt hct
      exact ⟨hrt, hct⟩
    have hcolw : extCol x z (col' w) col' w = col' w := extCol_o hwx hwz _ _
    have hcolv : extCol x z (col' w) col' v = col' v := extCol_o hvx hvz _ _
    have hlabw : extLab x z base lab' w = base + 1 := by rw [extLab_o hwx hwz, hAn.a1]
    have hlabv : extLab x z base lab' v = lab' v := extLab_o hvx hvz _ _
    have hgen : ∀ s ∈ S, s ≠ x → s ≠ z → s ≠ w → s ≠ v →
        s ∈ S' ∧ cut L A s = L s ∧ L s ∈ S' ∧ L s ≠ x ∧ L s ≠ z := by
      intro s hs h1 h2 h3 h4
      have hs' : s ∈ S' := (memS' s).2 ⟨h2, h1, hs⟩
      have hsA : s ∉ A := by rw [hmemA]; tauto
      have hc := cut_of_not_mem (L := L) hsA
      have hL' := hS'L s hs'
      rw [hc] at hL'
      obtain ⟨h5, h6, -⟩ := (memS' _).1 hL'
      exact ⟨hs', hc, hL', h6, h5⟩
    refine ⟨extCol x z (col' w) col', extLab x z base lab', b1, ?_, b3, b4, b5, ?_⟩
    · intro s hs hne
      by_cases h1 : s = x
      · rw [h1, hv, hcolv, extCol_x]; exact hcv
      by_cases h2 : s = z
      · rw [h2, hw, hcolw, extCol_z hzx]; simp
      by_cases h3 : s = w
      · rw [h3, hLw, hcolw, extCol_z hzx]; simp
      by_cases h4 : s = v
      · rw [h4, hLv, hcolv, extCol_x]; exact hcv.symm
      obtain ⟨hs', hc, -, hLx', hLz'⟩ := hgen s hs h1 h2 h3 h4
      rw [extCol_o hLx' hLz', extCol_o h1 h2]
      have := hG.c2 s hs' (by rw [hc]; exact hne)
      rwa [hc] at this
    · have hlong : ∀ s ∈ S, s ≠ x → L s ≠ s →
          extLab x z base lab' s + 2 ≤ extLab x z base lab' (L s) →
          s ∈ S' ∧ cut L A s = L s ∧ extLab x z base lab' s = lab' s ∧
          extLab x z base lab' (L s) = lab' (cut L A s) ∧ lab' v < lab' s := by
        intro s hs h1 hne hl
        by_cases h2 : s = z
        · rw [h2, hw, hlabw, extLab_z] at hl; omega
        by_cases h3 : s = w
        · rw [h3, hLw, hlabw, extLab_z] at hl; omega
        by_cases h4 : s = v
        · rw [h4, hLv, extLab_x] at hl
          have := (b5 v hvS).1; omega
        obtain ⟨hs', hc, -, hLx', hLz'⟩ := hgen s hs h1 h2 h3 h4
        have e1 := extLab_o h1 h2 base lab'
        have e2 : extLab x z base lab' (L s) = lab' (cut L A s) := by
          rw [hc, extLab_o hLx' hLz']
        refine ⟨hs', hc, e1, e2, ?_⟩
        have hnr : ¬ Reach ce (cut L A) w s := by
          intro hr
          have := hAn.a4 s hs' hr (by rw [hc]; exact hne)
          rw [e1, e2] at hl; omega
        exact hAn.a2 v hvS' s hs' hrv hnr
      intro s hs s' hs' hne hne' hl hl'
      by_cases h1 : s = x
      · by_cases h1' : s' = x
        · exact Or.inl (h1'.trans h1.symm)
        obtain ⟨-, -, e1', -, hlt⟩ := hlong s' hs' h1' hne' hl'
        right; right
        rw [h1, hv, hlabv, e1']; exact hlt
      by_cases h1' : s' = x
      · obtain ⟨-, -, e1, -, hlt⟩ := hlong s hs h1 hne hl
        right; left
        rw [h1', hv, hlabv, e1]; exact hlt
      obtain ⟨hsS, hc, e1, e2, -⟩ := hlong s hs h1 hne hl
      obtain ⟨hsS', hc', e1', e2', -⟩ := hlong s' hs' h1' hne' hl'
      rw [e1, e2] at hl
      rw [e1', e2'] at hl'
      rw [e1, e2, e1', e2']
      have := hG.c6 s hsS s' hsS' (by rw [hc]; exact hne) (by rw [hc']; exact hne') hl hl'
      rwa [hc, hc'] at this ⊢

theorem ihyp_all {ce : σ → σ} (hce : Function.Involutive ce) (hce0 : ∀ s, ce s ≠ s) :
    ∀ n, IHyp ce n := by
  intro n
  induction n with
  | zero => intro S L base h; omega
  | succ n ihn =>
    intro S L base hcard hL hSc hSL
    have ih : IHyp ce S.card := fun S' L' b' h => ihn S' L' b' (by omega)
    refine ⟨?_, fun y hy hLy => path_case hce hce0 ih hL hSc hSL base hy hLy⟩
    by_cases hfix : ∃ x ∈ S, L x = x
    · obtain ⟨x, hx, hLx⟩ := hfix
      obtain ⟨col, lab, hG, -⟩ := path_case hce hce0 ih hL hSc hSL base hx hLx
      exact ⟨col, lab, hG⟩
    · push Not at hfix
      by_cases hne : S.Nonempty
      · obtain ⟨x, hx⟩ := hne
        exact cycle_case hce hce0 ih hL hSc hSL base hx hfix
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        exact ⟨fun _ => true, fun _ => 0, by constructor <;> simp⟩

end SublinearChoresMMS.Disposal.Dev.LA2.PartG
end

section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartG
open Finset
set_option linter.unusedSectionVars false
theorem graph_structure {σ : Type} [Fintype σ] [DecidableEq σ] (ce le : σ → σ)
    (hce : Function.Involutive ce) (hce0 : ∀ s, ce s ≠ s) (hle : Function.Involutive le) :
    ∃ (col : σ → Bool) (lab : σ → ℕ),
      (∀ s, col (ce s) ≠ col s) ∧ (∀ s, le s ≠ s → col (le s) ≠ col s) ∧
      (∀ s, lab (ce s) = lab s) ∧ (∀ s s', lab s = lab s' → s' = s ∨ s' = ce s) ∧
      (∀ s, 2 * lab s < Fintype.card σ) ∧
      ∀ s s', le s ≠ s → le s' ≠ s' → lab s + 2 ≤ lab (le s) → lab s' + 2 ≤ lab (le s') →
        s' = s ∨ lab (le s') < lab s ∨ lab (le s) < lab s' := by
  obtain ⟨col, lab, hG⟩ := (ihyp_all hce hce0 (Fintype.card σ + 1) univ le 0
    (by simp) hle (by simp) (by simp)).1
  refine ⟨col, lab, fun s => hG.c1 s (mem_univ s), fun s => hG.c2 s (mem_univ s),
    fun s => hG.c3 s (mem_univ s), fun s s' => hG.c4 s (mem_univ s) s' (mem_univ s'),
    fun s => ?_, fun s s' => hG.c6 s (mem_univ s) s' (mem_univ s')⟩
  have := (hG.c5 s (mem_univ s)).2
  simpa [card_univ] using this

end SublinearChoresMMS.Disposal.Dev.LA2.PartG
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part G: chore-edges, local-edges, colours and labels -/
alias graph_structure := SublinearChoresMMS.Disposal.Dev.LA2.PartG.graph_structure

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartL
open SublinearChoresMMS.Disposal
open Finset
variable {σ : Type} [Fintype σ] [DecidableEq σ] {b : ℕ}
/-- The `K`-mass of bin `v` restricted to `S`, with `M` removed. -/
def lhs (loc : σ → Fin b) (w : σ → ℝ) (S K M : Finset σ) (v : Fin b) : ℝ :=
  ∑ s ∈ K, if s ∈ S ∧ loc s = v ∧ s ∉ M then w s else 0

/-- The total mass of bin `v` restricted to `S`. -/
def tot (loc : σ → Fin b) (w : σ → ℝ) (S : Finset σ) (v : Fin b) : ℝ :=
  ∑ s ∈ S, if loc s = v then w s else 0

/-- The statement for the copies in `S` (local-edges supported on `S`). -/
def Good (loc : σ → Fin b) (w : σ → ℝ) (S : Finset σ) : Prop :=
  ∃ le : σ → σ, Function.Involutive le ∧ (∀ s, loc (le s) = loc s) ∧ (∀ s, s ∉ S → le s = s) ∧
    ∀ K : Finset σ, (∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0) →
      ∀ v : Fin b, ∃ M : Finset σ, M ⊆ K ∧ M.card ≤ 1 ∧ (∀ s ∈ M, loc s = v) ∧
        lhs loc w S K M v ≤ tot loc w S v / 2

lemma tot_nonneg (loc : σ → Fin b) (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (S : Finset σ) (v : Fin b) :
    0 ≤ tot loc w S v :=
  Finset.sum_nonneg fun s _ => by
    split_ifs
    · exact hw s
    · exact le_rfl

lemma other_bin (loc : σ → Fin b) (w : σ → ℝ) {S S' : Finset σ} (hS' : S' ⊆ S) {v u : Fin b}
    (hloc : ∀ s ∈ S, s ∉ S' → loc s = v) (huv : u ≠ v) (K M : Finset σ) :
    lhs loc w S K M u = lhs loc w S' K M u ∧ tot loc w S u = tot loc w S' u := by
  constructor
  · unfold lhs
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h1 : s ∈ S'
    · simp [h1, hS' h1]
    · by_cases h2 : s ∈ S
      · have := hloc s h2 h1
        simp [h1, h2, this, Ne.symm huv]
      · simp [h1, h2]
  · unfold tot
    symm
    refine Finset.sum_subset hS' fun s hs hns => ?_
    simp [hloc s hs hns, Ne.symm huv]

lemma good_all (loc : σ → Fin b) (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (S : Finset σ) :
    Good loc w S := by
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    refine ⟨id, fun s => rfl, fun s => rfl, fun s _ => rfl,
      fun K _ v => ⟨∅, empty_subset _, by simp, by simp, ?_⟩⟩
    simp [lhs, tot]
  obtain ⟨s1, hs1S, hs1max⟩ := S.exists_max_image w hS
  rcases ((S.filter (fun s => loc s = loc s1)).erase s1).eq_empty_or_nonempty with hTe | hTne
  · -- `s1` is alone in its bin
    obtain ⟨le, hinv, hloc, hfix, hK⟩ := ih (S.erase s1) (Finset.erase_ssubset hs1S)
    refine ⟨le, hinv, hloc, fun s hs => hfix s (fun h => hs (Finset.mem_of_mem_erase h)),
      fun K hKh u => ?_⟩
    obtain ⟨M', hM'K, hM'c, hM'l, hM'⟩ := hK K hKh u
    by_cases huv : u = loc s1
    · subst huv
      refine ⟨K.filter (fun s => s = s1), filter_subset _ _, ?_, ?_, ?_⟩
      · refine (card_le_card (show K.filter (fun s => s = s1) ⊆ {s1} from
          fun s hs => ?_)).trans (by simp)
        simp only [mem_filter] at hs
        simp [hs.2]
      · intro s hs
        simp only [mem_filter] at hs
        rw [hs.2]
      · have h0 : lhs loc w S K (K.filter (fun s => s = s1)) (loc s1) = 0 := by
          unfold lhs
          refine Finset.sum_eq_zero fun s hsK => ?_
          rw [if_neg]
          rintro ⟨hsS, hsl, hsM⟩
          apply hsM
          have hss : s = s1 := by
            by_contra hne
            have hmem : s ∈ (S.filter (fun s => loc s = loc s1)).erase s1 := by
              simp [hne, hsS, hsl]
            rw [hTe] at hmem
            simp at hmem
          rw [hss] at hsK ⊢
          simp [hsK]
        rw [h0]
        exact div_nonneg (tot_nonneg loc w hw S _) two_pos.le
    · have hl : ∀ s ∈ S, s ∉ S.erase s1 → loc s = loc s1 := by
        intro s hs hns
        have : s = s1 := by
          by_contra hne
          exact hns (mem_erase.2 ⟨hne, hs⟩)
        rw [this]
      obtain ⟨h1, h2⟩ := other_bin loc w (erase_subset s1 S) hl huv K M'
      exact ⟨M', hM'K, hM'c, hM'l, by rw [h1, h2]; exact hM'⟩
  · -- pair `s1` with the next heaviest copy `s2` of its bin
    obtain ⟨s2, hs2T, hs2max⟩ := ((S.filter (fun s => loc s = loc s1)).erase s1).exists_max_image
      w hTne
    have hs2ne : s2 ≠ s1 := (mem_erase.1 hs2T).1
    have hs2S : s2 ∈ S := (mem_filter.1 (mem_erase.1 hs2T).2).1
    have hs2l : loc s2 = loc s1 := (mem_filter.1 (mem_erase.1 hs2T).2).2
    have hw21 : w s2 ≤ w s1 := hs1max s2 hs2S
    obtain ⟨S', hS'⟩ : ∃ S', S' = (S.erase s1).erase s2 := ⟨_, rfl⟩
    have hmemS' : ∀ s, s ∈ S' ↔ s ≠ s2 ∧ s ≠ s1 ∧ s ∈ S := by
      intro s; simp [hS']
    have hS'sub : S' ⊂ S := by
      rw [hS']
      exact Finset.ssubset_of_subset_of_ssubset (erase_subset _ _) (erase_ssubset hs1S)
    have hS'le : S' ⊆ S := hS'sub.subset
    have hout : ∀ s ∈ S, s ∉ S' → s = s1 ∨ s = s2 := by
      intro s hs hns
      by_contra hc
      push Not at hc
      exact hns ((hmemS' s).2 ⟨hc.2, hc.1, hs⟩)
    obtain ⟨le, hinv, hloc, hfix, hK⟩ := ih S' hS'sub
    have hle1 : le s1 = s1 := hfix s1 (by simp [hmemS'])
    have hle2 : le s2 = s2 := hfix s2 (by simp [hmemS'])
    let le' : σ → σ := fun s => if s = s1 then s2 else if s = s2 then s1 else le s
    have hle'1 : le' s1 = s2 := by simp [le']
    have hle'o : ∀ s, s ≠ s1 → s ≠ s2 → le' s = le s := by
      intro s h1 h2; simp [le', h1, h2]
    have hinv' : Function.Involutive le' := by
      intro s
      by_cases h1 : s = s1
      · simp [le', h1, hs2ne]
      by_cases h2 : s = s2
      · simp [le', h2, hs2ne]
      have h3 : le s ≠ s1 := fun h => h1 (by rw [← hinv s, h, hle1])
      have h4 : le s ≠ s2 := fun h => h2 (by rw [← hinv s, h, hle2])
      simp [le', h1, h2, h3, h4, hinv s]
    have hloc' : ∀ s, loc (le' s) = loc s := by
      intro s
      by_cases h1 : s = s1
      · simp [le', h1, hs2l]
      by_cases h2 : s = s2
      · simp [le', h2, hs2ne, hs2l]
      simp [le', h1, h2, hloc s]
    have hfix' : ∀ s, s ∉ S → le' s = s := by
      intro s hs
      have h1 : s ≠ s1 := fun h => hs (h ▸ hs1S)
      have h2 : s ≠ s2 := fun h => hs (h ▸ hs2S)
      rw [hle'o s h1 h2]
      exact hfix s fun h => hs (hS'le h)
    refine ⟨le', hinv', hloc', hfix', fun K hKh u => ?_⟩
    have hKh0 : ∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0 := by
      intro s hs hne hmem
      have hsS' : s ∈ S' := by
        by_contra h
        exact hne (hfix s h)
      have h1 : s ≠ s1 := ((hmemS' s).1 hsS').2.1
      have h2 : s ≠ s2 := ((hmemS' s).1 hsS').1
      rw [← hle'o s h1 h2] at hne hmem ⊢
      exact hKh s hs hne hmem
    obtain ⟨M', hM'K, hM'c, hM'l, hM'⟩ := hK K hKh0 u
    by_cases huv : u = loc s1
    · subst huv
      have hSeq : S = insert s1 (insert s2 S') := by
        rw [hS', insert_erase (mem_erase.2 ⟨hs2ne, hs2S⟩), insert_erase hs1S]
      have htot : tot loc w S (loc s1) = tot loc w S' (loc s1) + w s1 + w s2 := by
        have hn1 : s1 ∉ insert s2 S' := by simp [hmemS', hs2ne.symm]
        have hn2 : s2 ∉ S' := by simp [hmemS']
        conv_lhs => rw [hSeq]
        unfold tot
        rw [sum_insert hn1, sum_insert hn2]
        simp [hs2l]
        ring
      have hT : ∀ s ∈ S', loc s = loc s1 → w s ≤ w s2 := by
        intro s hs hl
        obtain ⟨_, h1, h3⟩ := (hmemS' s).1 hs
        exact hs2max s (by simp [h1, h3, hl])
      have key : ∀ x, x ∈ K → (∀ s ∈ K, (s = s1 ∨ s = s2) → s ≠ x → w s = 0) →
          lhs loc w S K {x} (loc s1) ≤ tot loc w S (loc s1) / 2 := by
        intro x _ hzero
        have hpt : lhs loc w S K {x} (loc s1) ≤ lhs loc w S' K M' (loc s1) +
            ∑ s ∈ K, if s ∈ M' ∧ s ∈ S' ∧ loc s = loc s1 then w s else 0 := by
          unfold lhs
          rw [← sum_add_distrib]
          refine sum_le_sum fun s hs => ?_
          simp only [mem_singleton]
          by_cases hsS' : s ∈ S'
          · have hsS : s ∈ S := hS'le hsS'
            split_ifs <;> first | linarith [hw s] | tauto
          · have hz' : s ∈ S → s ≠ x → w s = 0 := fun h h' => hzero s hs (hout s h hsS') h'
            have e1 : (if s ∈ S' ∧ loc s = loc s1 ∧ s ∉ M' then w s else 0) = 0 :=
              if_neg fun h => hsS' h.1
            have e2 : (if s ∈ M' ∧ s ∈ S' ∧ loc s = loc s1 then w s else 0) = 0 :=
              if_neg fun h => hsS' h.2.1
            rw [e1, e2, add_zero]
            split_ifs with h
            · exact (hz' h.1 h.2.2).le
            · exact le_rfl
        have hg : (∑ s ∈ K, if s ∈ M' ∧ s ∈ S' ∧ loc s = loc s1 then w s else 0) ≤ w s2 := by
          rw [← Finset.sum_filter]
          have hc : (K.filter fun s => s ∈ M' ∧ s ∈ S' ∧ loc s = loc s1).card ≤ 1 :=
            (card_le_card fun s hs => (mem_filter.1 hs).2.1).trans hM'c
          calc _ ≤ (K.filter fun s => s ∈ M' ∧ s ∈ S' ∧ loc s = loc s1).card • w s2 :=
                Finset.sum_le_card_nsmul _ _ _ fun s hs =>
                  hT s (mem_filter.1 hs).2.2.1 (mem_filter.1 hs).2.2.2
            _ ≤ w s2 := by
                rw [nsmul_eq_mul]
                exact mul_le_of_le_one_left (hw s2) (by exact_mod_cast hc)
        linarith
      by_cases hp1 : s1 ∈ K ∧ 0 < w s1
      · refine ⟨{s1}, by simpa using hp1.1, by simp, by simp, key s1 hp1.1 ?_⟩
        intro s hs hs12 hne
        rcases hs12 with h | h
        · exact absurd h hne
        subst h
        have := hKh s1 hp1.1 (by rw [hle'1]; exact hs2ne) (by rw [hle'1]; exact hs)
        rw [hle'1] at this
        rcases this with h | h
        · linarith [hp1.2]
        · exact h
      by_cases hp2 : s2 ∈ K ∧ 0 < w s2
      · refine ⟨{s2}, by simpa using hp2.1, by simp, by simp [hs2l], key s2 hp2.1 ?_⟩
        intro s hs hs12 hne
        rcases hs12 with h | h
        · subst h
          have : ¬ 0 < w s := fun h' => hp1 ⟨hs, h'⟩
          linarith [hw s]
        · exact absurd h hne
      · refine ⟨M', hM'K, hM'c, hM'l, ?_⟩
        have hz : ∀ s ∈ K, (s = s1 ∨ s = s2) → w s = 0 := by
          intro s hs h
          rcases h with h | h
          · subst h
            have : ¬ 0 < w s := fun h' => hp1 ⟨hs, h'⟩
            linarith [hw s]
          · subst h
            have : ¬ 0 < w s := fun h' => hp2 ⟨hs, h'⟩
            linarith [hw s]
        have hpt : lhs loc w S K M' (loc s1) ≤ lhs loc w S' K M' (loc s1) := by
          unfold lhs
          refine sum_le_sum fun s hs => ?_
          by_cases hsS' : s ∈ S'
          · simp [hsS', hS'le hsS']
          · have e1 : (if s ∈ S' ∧ loc s = loc s1 ∧ s ∉ M' then w s else 0) = 0 :=
              if_neg fun h => hsS' h.1
            rw [e1]
            split_ifs with h
            · exact (hz s hs (hout s h.1 hsS')).le
            · exact le_rfl
        linarith [hw s1, hw s2]
    · have hl : ∀ s ∈ S, s ∉ S' → loc s = loc s1 := by
        intro s hs hns
        rcases hout s hs hns with h | h
        · rw [h]
        · rw [h, hs2l]
      obtain ⟨h1, h2⟩ := other_bin loc w hS'le hl huv K M'
      exact ⟨M', hM'K, hM'c, hM'l, by rw [h1, h2]; exact hM'⟩

end SublinearChoresMMS.Disposal.Dev.LA2.PartL
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartL
open SublinearChoresMMS.Disposal
open Finset
/-- Pair the copies of each bin consecutively in decreasing cost. If a set `K` of copies has at most
one copy of positive cost on every local-edge, then removing at most one copy of `K` per bin leaves
at most half the bin's original cost in `K`. -/
theorem local_edges {σ : Type} [Fintype σ] [DecidableEq σ] {b : ℕ} (loc : σ → Fin b)
    (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) :
    ∃ le : σ → σ, Function.Involutive le ∧ (∀ s, loc (le s) = loc s) ∧
      ∀ K : Finset σ, (∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0) →
        ∀ v : Fin b, ∃ M : Finset σ, M ⊆ K ∧ M.card ≤ 1 ∧ (∀ s ∈ M, loc s = v) ∧
          (∑ s ∈ K, if loc s = v ∧ s ∉ M then w s else 0) ≤
            (∑ s ∈ univ.filter (fun s => loc s = v), w s) / 2 := by
  obtain ⟨le, hinv, hloc, -, hK⟩ := good_all loc w hw univ
  refine ⟨le, hinv, hloc, fun K hKh v => ?_⟩
  obtain ⟨M, hMK, hMc, hMl, hM⟩ := hK K hKh v
  refine ⟨M, hMK, hMc, hMl, ?_⟩
  have e1 : lhs loc w univ K M v = ∑ s ∈ K, if loc s = v ∧ s ∉ M then w s else 0 := by
    simp [lhs]
  have e2 : tot loc w univ v = ∑ s ∈ univ.filter (fun s => loc s = v), w s := by
    simp [tot, sum_filter]
  rw [e1, e2] at hM
  exact hM

end SublinearChoresMMS.Disposal.Dev.LA2.PartL
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part L: local-edges inside a bin (Step 3, the set-aside bins) -/
alias local_edges := SublinearChoresMMS.Disposal.Dev.LA2.PartL.local_edges

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartC
open SublinearChoresMMS.Disposal.Dev.LA2
open Finset
/-! ### Signs, retained sets -/
/-- `+1` for blue (`true`), `-1` for red (`false`). -/
def sgnB (c : Bool) : ℝ := if c then 1 else -1

lemma abs_sgnB (c : Bool) : |sgnB c| = 1 := by cases c <;> simp [sgnB]

open Classical in
/-- The retained copies for the polynomial values `P` and tie-break colour `e`. -/
def keepSet {σ : Type} [Fintype σ] (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ) (e : Bool) :
    Finset σ :=
  univ.filter (fun s => (P (lab s) ≠ 0 → sgnB (col s) * P (lab s) < 0) ∧
    (P (lab s) = 0 → col s = e))

lemma mem_keepSet {σ : Type} [Fintype σ] (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ) (e : Bool)
    (s : σ) : s ∈ keepSet col lab P e ↔ (P (lab s) ≠ 0 → sgnB (col s) * P (lab s) < 0) ∧
      (P (lab s) = 0 → col s = e) := by
  simp [keepSet]

lemma bool_ne {x y : Bool} (h : x ≠ y) : x = !y := by cases x <;> cases y <;> simp_all

lemma keep_ce {σ : Type} [Fintype σ] (ce : σ → σ) (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ)
    (e : Bool) (hcce : ∀ s, col (ce s) ≠ col s) (hlce : ∀ s, lab (ce s) = lab s) (s : σ) :
    s ∈ keepSet col lab P e ↔ ce s ∉ keepSet col lab P e := by
  rw [mem_keepSet, mem_keepSet, hlce, bool_ne (hcce s)]
  by_cases hP : P (lab s) = 0
  · cases h : col s <;> cases e <;> simp [hP]
  · rcases lt_or_gt_of_ne hP with h2 | h2 <;> cases h : col s <;>
      simp [sgnB, hP] <;> constructor <;> intro <;> linarith

lemma keep_compl {σ : Type} [Fintype σ] (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ) (s : σ) :
    s ∈ keepSet col lab P true ↔ s ∉ keepSet col lab (fun x => -P x) false := by
  rw [mem_keepSet, mem_keepSet]
  by_cases hP : P (lab s) = 0
  · cases col s <;> simp [hP]
  · have : sgnB (col s) * P (lab s) ≠ 0 := mul_ne_zero (by cases col s <;> simp [sgnB]) hP
    simp only [hP, ne_eq, neg_eq_zero, not_false_eq_true, forall_const, IsEmpty.forall_iff,
      and_true, mul_neg, Left.neg_neg_iff, not_lt]
    constructor
    · intro h; linarith
    · intro h; exact lt_of_le_of_ne h this

/-! ### Polynomials -/
lemma polyEval_continuous {d : ℕ} (z : Fin (d + 1) → ℝ) : Continuous (polyEval z) := by
  unfold polyEval; fun_prop

lemma poly_roots {d : ℕ} (z : Fin (d + 1) → ℝ) (hz : z ≠ 0) :
    ∃ R : Finset ℝ, R.card ≤ d ∧ ∀ x, polyEval z x = 0 → x ∈ R := by
  classical
  set Q : Polynomial ℝ := ∑ a, Polynomial.C (z a) * Polynomial.X ^ (a : ℕ) with hQ
  have heval : ∀ x, Q.eval x = polyEval z x := by
    intro x; simp [hQ, polyEval, Polynomial.eval_finsetSum]
  have hcoeff : ∀ a : Fin (d + 1), Q.coeff a = z a := by
    intro a
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro h; exact hc (Fin.ext h.symm)
    · simp
  have hQ0 : Q ≠ 0 := by
    intro h; apply hz; funext a; rw [← hcoeff a, h]; simp
  have hdeg : Q.natDegree ≤ d := by
    rw [hQ]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp a.isLt)
  refine ⟨Q.roots.toFinset, ?_, ?_⟩
  · exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' Q).trans hdeg)
  · intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, heval]
    exact hx

lemma root_between {P : ℝ → ℝ} (hP : Continuous P) {x y : ℝ} (hxy : x < y)
    (h : P x * P y < 0) : ∃ r, x < r ∧ r < y ∧ P r = 0 := by
  rcases lt_or_gt_of_ne (show P x ≠ 0 by rintro h0; simp [h0] at h) with hx | hx
  · have hy : 0 < P y := by nlinarith
    obtain ⟨r, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo hxy.le hP.continuousOn ⟨hx, hy⟩
    exact ⟨r, h1, h2, h3⟩
  · have hy : P y < 0 := by nlinarith
    obtain ⟨r, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' hxy.le hP.continuousOn ⟨hy, hx⟩
    exact ⟨r, h1, h2, h3⟩

lemma sgn_sign {c : Bool} {p : ℝ} (h : sgnB c * p < 0) : sgnB c * Real.sign p = -1 := by
  cases c <;> simp only [sgnB] at h ⊢ <;> simp at h ⊢
  · rw [Real.sign_of_pos (by linarith)]
  · rw [Real.sign_of_neg h]

/-! ### Counting the marks of Step 2 -/
lemma card_Z {σ : Type} [Fintype σ] [DecidableEq σ] (ce : σ → σ) (lab : σ → ℕ) (P : ℝ → ℝ)
    (keep : Finset σ) (hkc : ∀ s, s ∈ keep ↔ ce s ∉ keep)
    (hlu : ∀ s s', lab s = lab s' → s' = s ∨ s' = ce s)
    (R : Finset ℝ) (hR : ∀ x, P x = 0 → x ∈ R) :
    (keep.filter (fun s => P (lab s) = 0)).card ≤ R.card := by
  classical
  apply card_le_card_of_injOn (fun s => (lab s : ℝ))
  · intro s hs
    rw [mem_coe, mem_filter] at hs
    exact hR _ hs.2
  · intro s hs s' hs' h
    rw [mem_coe, mem_filter] at hs hs'
    have h2 : (lab s : ℝ) = lab s' := h
    have h' : lab s = lab s' := by exact_mod_cast h2
    rcases hlu s s' h' with h1 | h1
    · exact h1.symm
    · exact absurd (h1 ▸ hs'.1) ((hkc s).1 hs.1)

open Classical in
/-- The copies marked on local-edges with two retained endpoints of positive cost (the endpoint
with the larger label). -/
def Lset {σ : Type} (keep : Finset σ) (le : σ → σ) (w : σ → ℝ) (lab : σ → ℕ) (P : ℝ → ℝ) :
    Finset σ :=
  keep.filter (fun s => P (lab s) ≠ 0 ∧ 0 < w s ∧ le s ≠ s ∧ le s ∈ keep ∧
    P (lab (le s)) ≠ 0 ∧ 0 < w (le s) ∧ lab (le s) < lab s)

lemma mem_Lset {σ : Type} (keep : Finset σ) (le : σ → σ) (w : σ → ℝ) (lab : σ → ℕ)
    (P : ℝ → ℝ) (s : σ) : s ∈ Lset keep le w lab P ↔ s ∈ keep ∧ P (lab s) ≠ 0 ∧ 0 < w s ∧
      le s ≠ s ∧ le s ∈ keep ∧ P (lab (le s)) ≠ 0 ∧ 0 < w (le s) ∧ lab (le s) < lab s := by
  simp [Lset]

lemma L_root {σ : Type} [Fintype σ] (le : σ → σ) (w : σ → ℝ) (col : σ → Bool) (lab : σ → ℕ)
    (P : ℝ → ℝ) (hP : Continuous P) (e : Bool) (hcle : ∀ s, le s ≠ s → col (le s) ≠ col s)
    (s : σ) (hs : s ∈ Lset (keepSet col lab P e) le w lab P) :
    ∃ r, (lab (le s) : ℝ) < r ∧ r < lab s ∧ P r = 0 := by
  rw [mem_Lset] at hs
  obtain ⟨hk1, hP1, -, hls, hk2, hP2, -, hlt⟩ := hs
  have h1 := ((mem_keepSet _ _ _ _ _).1 hk1).1 hP1
  have h2 := ((mem_keepSet _ _ _ _ _).1 hk2).1 hP2
  rw [bool_ne (hcle s hls)] at h2
  have hprod : P (lab (le s)) * P (lab s) < 0 := by
    cases h : col s <;> simp only [sgnB, h] at h1 h2 <;> simp at h1 h2 <;> nlinarith
  exact root_between hP (by exact_mod_cast hlt) hprod

lemma card_L {σ : Type} [Fintype σ] [DecidableEq σ] (ce le : σ → σ) (w : σ → ℝ)
    (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ) (hP : Continuous P) (e : Bool)
    (hle : Function.Involutive le) (hcle : ∀ s, le s ≠ s → col (le s) ≠ col s)
    (hlu : ∀ s s', lab s = lab s' → s' = s ∨ s' = ce s)
    (hclose : ∀ s s', le s ≠ s → le s' ≠ s' → lab s + 2 ≤ lab (le s) →
      lab s' + 2 ≤ lab (le s') → s' = s ∨ lab (le s') < lab s ∨ lab (le s) < lab s')
    (R : Finset ℝ) (hR : ∀ x, P x = 0 → x ∈ R) :
    (Lset (keepSet col lab P e) le w lab P).card ≤ 3 * R.card := by
  classical
  set L := Lset (keepSet col lab P e) le w lab P with hL
  have hroot : ∀ s, ∃ r : ℝ, s ∈ L → (lab (le s) : ℝ) < r ∧ r < lab s ∧ P r = 0 := by
    intro s
    by_cases hs : s ∈ L
    · obtain ⟨r, hr⟩ := L_root le w col lab P hP e hcle s hs
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose f hf using hroot
  have hlt : ∀ s ∈ L, lab (le s) < lab s := fun s hs => ((mem_Lset _ _ _ _ _ _).1 hs).2.2.2.2.2.2.2
  have hne : ∀ s ∈ L, le s ≠ s := fun s hs => ((mem_Lset _ _ _ _ _ _).1 hs).2.2.2.1
  set L1 := L.filter (fun s => lab s = lab (le s) + 1)
  set L2 := L.filter (fun s => ¬ lab s = lab (le s) + 1)
  have hsplit : L1.card + L2.card = L.card := card_filter_add_card_filter_not _
  -- gap-one edges: the label is determined by the root, two copies per label
  have h1 : L1.card ≤ 2 * R.card := by
    have hA : L1.card ≤ 2 * (L1.image lab).card := by
      apply card_le_mul_card_image
      intro m hm
      obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hm
      calc (L1.filter (fun a => lab a = lab s0)).card ≤ ({s0, ce s0} : Finset σ).card := by
            apply card_le_card
            intro a ha
            rw [mem_filter] at ha
            rcases hlu s0 a ha.2.symm with h | h <;> simp [h]
        _ ≤ 2 := card_le_two
    have hB : (L1.image lab).card ≤ R.card := by
      calc (L1.image lab).card ≤ (R.image (fun x => ⌊x⌋₊ + 1)).card := by
            apply card_le_card
            intro m hm
            obtain ⟨s, hs, rfl⟩ := mem_image.1 hm
            rw [mem_filter] at hs
            obtain ⟨h1, h2, h3⟩ := hf s hs.1
            rw [mem_image]
            refine ⟨f s, hR _ h3, ?_⟩
            have hfl : ⌊f s⌋₊ = lab (le s) := by
              rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg (lab (le s)) : (0:ℝ) ≤ _)])]
              refine ⟨h1.le, ?_⟩
              have : (lab s : ℝ) = lab (le s) + 1 := by exact_mod_cast hs.2
              linarith
            rw [hfl, hs.2]
        _ ≤ R.card := card_image_le
    omega
  have h2 : L2.card ≤ R.card := by
    apply card_le_card_of_injOn f
    · intro s hs
      rw [mem_coe, mem_filter] at hs
      exact hR _ (hf s hs.1).2.2
    · intro s hs s' hs' hss
      rw [mem_coe, mem_filter] at hs hs'
      have hg1 : lab (le s) + 2 ≤ lab s := by have := hlt s hs.1; omega
      have hg2 : lab (le s') + 2 ≤ lab s' := by have := hlt s' hs'.1; omega
      have hn1 : le (le s) ≠ le s := by rw [hle s]; exact fun h => hne s hs.1 h.symm
      have hn2 : le (le s') ≠ le s' := by rw [hle s']; exact fun h => hne s' hs'.1 h.symm
      have := hclose (le s) (le s') hn1 hn2 (by rw [hle s]; exact hg1) (by rw [hle s']; exact hg2)
      rw [hle s, hle s'] at this
      obtain ⟨a1, a2, -⟩ := hf s hs.1
      obtain ⟨b1, b2, -⟩ := hf s' hs'.1
      rcases this with h | h | h
      · have := congrArg le h; rw [hle, hle] at this; exact this.symm
      · have : (lab s' : ℝ) < lab (le s) := by exact_mod_cast h
        rw [hss] at a1 a2; linarith
      · have : (lab s : ℝ) < lab (le s') := by exact_mod_cast h
        rw [hss] at a1 a2; linarith
  omega

/-! ### Bin loads -/
/-- The bin difference `D_v(α)`. -/
def Dfun {σ : Type} [Fintype σ] {b : ℕ} (loc : σ → Fin b) (w : σ → ℝ) (col : σ → Bool)
    (lab : σ → ℕ) (a : ℕ → ℝ) (x : Fin b) : ℝ :=
  ∑ s ∈ univ.filter (fun s => loc s = x), w s * sgnB (col s) * a (lab s)

lemma Dfun_neg {σ : Type} [Fintype σ] {b : ℕ} (loc : σ → Fin b) (w : σ → ℝ) (col : σ → Bool)
    (lab : σ → ℕ) (a : ℕ → ℝ) (x : Fin b) :
    Dfun loc w col lab (fun n => -a n) x = - Dfun loc w col lab a x := by
  unfold Dfun; rw [← sum_neg_distrib]; refine sum_congr rfl (fun s _ => by ring)

lemma bin_main {σ : Type} [Fintype σ] [DecidableEq σ] {b : ℕ} (loc : σ → Fin b) (w : σ → ℝ)
    (hw : ∀ s, 0 ≤ w s) (col : σ → Bool) (lab : σ → ℕ) (P : ℝ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ s, |a (lab s)| ≤ 1) (has : ∀ s, P (lab s) ≠ 0 → a (lab s) = Real.sign (P (lab s)))
    (keep newM : Finset σ) (hk : ∀ s ∈ keep, P (lab s) ≠ 0 → sgnB (col s) * P (lab s) < 0)
    (hZ : ∀ s ∈ keep, s ∉ newM → P (lab s) ≠ 0) (x : Fin b) :
    (∑ s ∈ keep, if s ∉ newM ∧ loc s = x then w s else 0) ≤
      ((∑ s ∈ univ.filter (fun s => loc s = x), w s) - Dfun loc w col lab a x) / 2 := by
  classical
  have hterm : ∀ s, 0 ≤ w s * (1 - sgnB (col s) * a (lab s)) / 2 := by
    intro s
    have h := ha s
    have h2 : |sgnB (col s) * a (lab s)| ≤ 1 := by rw [abs_mul, abs_sgnB, one_mul]; exact h
    have h3 := (abs_le.mp h2).2
    exact div_nonneg (mul_nonneg (hw s) (by linarith)) (by norm_num)
  have hrhs : ((∑ s ∈ univ.filter (fun s => loc s = x), w s) - Dfun loc w col lab a x) / 2 =
      ∑ s ∈ univ.filter (fun s => loc s = x), w s * (1 - sgnB (col s) * a (lab s)) / 2 := by
    unfold Dfun; rw [← sum_sub_distrib, sum_div]; exact sum_congr rfl (fun s _ => by ring)
  rw [hrhs, ← sum_filter]
  calc ∑ s ∈ keep.filter (fun s => s ∉ newM ∧ loc s = x), w s
      = ∑ s ∈ keep.filter (fun s => s ∉ newM ∧ loc s = x),
          w s * (1 - sgnB (col s) * a (lab s)) / 2 := by
        refine sum_congr rfl (fun s hs => ?_)
        rw [mem_filter] at hs
        have hP := hZ s hs.1 hs.2.1
        rw [has s hP, sgn_sign (hk s hs.1 hP)]; ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (by intro s hs; rw [mem_filter] at hs ⊢; exact ⟨mem_univ _, hs.2.2⟩)
        (fun s _ _ => hterm s)

lemma bin_U {σ : Type} [Fintype σ] [DecidableEq σ] {b : ℕ} (loc : σ → Fin b) (w : σ → ℝ)
    (hw : ∀ s, 0 ≤ w s) (keep newM K M : Finset σ) (x : Fin b)
    (hsub : ∀ s ∈ keep, s ∉ newM → s ∈ K ∧ s ∉ M) (W : ℝ)
    (hM : (∑ s ∈ K, if loc s = x ∧ s ∉ M then w s else 0) ≤ W) :
    (∑ s ∈ keep, if s ∉ newM ∧ loc s = x then w s else 0) ≤ W := by
  classical
  rw [← sum_filter] at hM ⊢
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun s _ _ => hw s)) hM
  intro s hs
  rw [mem_filter] at hs ⊢
  have := hsub s hs.1 hs.2.1
  exact ⟨this.1, hs.2.2, this.2⟩

lemma pair_split {σ : Type} [DecidableEq σ] {b : ℕ} (S newM : Finset σ) (loc : σ → Fin b)
    (w : σ → ℝ) {x y : Fin b} (hxy : x ≠ y) :
    (∑ s ∈ S, if s ∉ newM ∧ (loc s = x ∨ loc s = y) then w s else 0) =
      (∑ s ∈ S, if s ∉ newM ∧ loc s = x then w s else 0) +
        (∑ s ∈ S, if s ∉ newM ∧ loc s = y then w s else 0) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun s _ => ?_)
  by_cases h1 : s ∈ newM <;> by_cases h2 : loc s = x <;> by_cases h3 : loc s = y <;> simp_all

/-! ### Pairings -/
lemma E_cases {b B : ℕ} {u v : Fin b} (E : Fin B ≃ {x : Fin b // x ≠ u ∧ x ≠ v}) (x : Fin b) :
    x = u ∨ x = v ∨ ∃ i, x = (E i).1 := by
  by_cases h : x = u
  · exact Or.inl h
  by_cases h' : x = v
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr ⟨E.symm ⟨x, h, h'⟩, by simp⟩)

lemma pairing_ext {b B : ℕ} (u v : Fin b) (huv : u ≠ v)
    (E : Fin B ≃ {x : Fin b // x ≠ u ∧ x ≠ v})
    (τ : Fin B → Fin B) (hτ : Function.Involutive τ) (hτ0 : ∀ r, τ r ≠ r) :
    ∃ π : Fin b → Fin b, Function.Involutive π ∧ (∀ x, π x ≠ x) ∧ π u = v ∧ π v = u ∧
      ∀ i, π (E i).1 = (E (τ i)).1 := by
  let π : Fin b → Fin b := fun x =>
    if h : x = u then v else if h' : x = v then u else (E (τ (E.symm ⟨x, h, h'⟩))).1
  have hE : ∀ i, π (E i).1 = (E (τ i)).1 := by
    intro i
    have h1 := (E i).2
    simp only [π, dif_neg h1.1, dif_neg h1.2]
    simp
  have hu : π u = v := by simp [π]
  have hv : π v = u := by simp [π, huv.symm]
  refine ⟨π, ?_, ?_, hu, hv, hE⟩
  · intro x
    rcases E_cases E x with rfl | rfl | ⟨i, rfl⟩
    · rw [hu, hv]
    · rw [hv, hu]
    · rw [hE, hE, hτ]
  · intro x
    rcases E_cases E x with rfl | rfl | ⟨i, rfl⟩
    · rw [hu]; exact huv.symm
    · rw [hv]; exact huv
    · rw [hE]; intro h; exact hτ0 i (E.injective (Subtype.ext h))

lemma card_top (B N : ℕ) : (univ.filter (fun r : Fin B => N ≤ r.val)).card ≤ B - N := by
  calc _ ≤ (Finset.Ico N B).card := by
        apply card_le_card_of_injOn (fun r => r.val)
        · intro r hr
          rw [mem_coe, mem_filter] at hr
          rw [mem_coe, Finset.mem_Ico]
          exact ⟨hr.2, r.isLt⟩
        · intro r _ r' _ h; exact Fin.ext h
    _ = B - N := Nat.card_Ico N B

lemma rank_pairing (B b' g d : ℕ) (hB : B = 2 * b') (hg : 1 ≤ g) (hgb : g ≤ b')
    (hgd : b' < g * d) :
    ∃ ρ : Fin B → Fin B, Function.Involutive ρ ∧ (∀ r, ρ r ≠ r) ∧
      (∀ r : Fin B, B - 2 * g ≤ r.val → B - 2 * g ≤ (ρ r).val) ∧
      ∀ r : Fin B, r.val < B - 2 * g → ∃ a : Fin d,
        (r.val + 1 ≤ min b' ((a.val + 1) * g) ∧ (ρ r).val + min b' ((a.val + 1) * g) ≤ B) ∨
        ((ρ r).val + 1 ≤ min b' ((a.val + 1) * g) ∧ r.val + min b' ((a.val + 1) * g) ≤ B) := by
  set N := B - 2 * g with hN
  let f : ℕ → ℕ := fun r => if r < N then N - 1 - r else if (r - N) % 2 = 0 then r + 1 else r - 1
  have hfB : ∀ r < B, f r < B := by intro r hr; simp only [f]; split_ifs <;> omega
  have hf2 : ∀ r < B, f (f r) = r := by intro r hr; simp only [f]; split_ifs <;> omega
  have hf0 : ∀ r < B, f r ≠ r := by intro r hr; simp only [f]; split_ifs <;> omega
  have hfN : ∀ r < B, N ≤ r → N ≤ f r := by intro r hr; simp only [f]; split_ifs <;> omega
  have key : ∀ r, r < b' - g → ∃ a : Fin d,
      r + 1 ≤ min b' ((a.val + 1) * g) ∧ (N - 1 - r) + min b' ((a.val + 1) * g) ≤ B := by
    intro r hr
    have hm1 : r / g * g ≤ r := Nat.div_mul_le_self r g
    have hm2 : r < r / g * g + g := Nat.lt_div_mul_add (by omega)
    have had : r / g < d := by
      rw [Nat.div_lt_iff_lt_mul (by omega), mul_comm]; omega
    refine ⟨⟨r / g, had⟩, ?_⟩
    have : (r / g + 1) * g = r / g * g + g := by ring
    simp only
    rw [this]; omega
  refine ⟨fun r => ⟨f r.val, hfB r.val r.isLt⟩, ?_, ?_, ?_, ?_⟩
  · intro r; ext; exact hf2 r.val r.isLt
  · intro r h; exact hf0 r.val r.isLt (congrArg Fin.val h)
  · intro r h; exact hfN r.val r.isLt h
  · intro r hr
    have hfr : f r.val = N - 1 - r.val := if_pos hr
    by_cases h : r.val < b' - g
    · obtain ⟨a, ha1, ha2⟩ := key r.val h
      exact ⟨a, Or.inl ⟨ha1, by simp only [hfr]; exact ha2⟩⟩
    · obtain ⟨a, ha1, ha2⟩ := key (N - 1 - r.val) (by omega)
      refine ⟨a, Or.inr ⟨by simp only [hfr]; exact ha1, ?_⟩⟩
      have : N - 1 - (N - 1 - r.val) = r.val := by omega
      rw [this] at ha2; exact ha2

lemma pair_from_rank {B d : ℕ} (Y : Fin B → ℝ) (hY : ∀ i j : Fin B, i ≤ j → Y j ≤ Y i)
    (k : Fin d → ℕ)
    (hk : ∀ a (i j : Fin B), i.val + 1 = k a → j.val + k a = B → Y i + Y j = 0)
    (r r' : Fin B) (a : Fin d) (h1 : r.val + 1 ≤ k a) (h2 : r'.val + k a ≤ B) :
    0 ≤ Y r + Y r' := by
  have hi : k a - 1 < B := by omega
  have hj : B - k a < B := by omega
  have h0 := hk a ⟨k a - 1, hi⟩ ⟨B - k a, hj⟩ (by simp only; omega) (by simp only; omega)
  have h3 := hY r ⟨k a - 1, hi⟩ (by rw [Fin.le_def]; simp only; omega)
  have h4 := hY r' ⟨B - k a, hj⟩ (by rw [Fin.le_def]; simp only; omega)
  linarith

/-! ### Steps 2 and 3 for a fixed orientation -/
theorem main {σ : Type} [Fintype σ] [DecidableEq σ] {b B d g N : ℕ}
    (loc : σ → Fin b) (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (T : Fin b → ℝ)
    (hW : ∀ v, ∑ s ∈ univ.filter (fun s => loc s = v), w s ≤ T v)
    (ce le : σ → σ) (hle : Function.Involutive le)
    (hK : ∀ K : Finset σ, (∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0) →
        ∀ v : Fin b, ∃ M : Finset σ, M ⊆ K ∧ M.card ≤ 1 ∧ (∀ s ∈ M, loc s = v) ∧
          (∑ s ∈ K, if loc s = v ∧ s ∉ M then w s else 0) ≤
            (∑ s ∈ univ.filter (fun s => loc s = v), w s) / 2)
    (col : σ → Bool) (lab : σ → ℕ)
    (hcce : ∀ s, col (ce s) ≠ col s) (hcle : ∀ s, le s ≠ s → col (le s) ≠ col s)
    (hlce : ∀ s, lab (ce s) = lab s) (hlu : ∀ s s', lab s = lab s' → s' = s ∨ s' = ce s)
    (hclose : ∀ s s', le s ≠ s → le s' ≠ s' → lab s + 2 ≤ lab (le s) →
      lab s' + 2 ≤ lab (le s') → s' = s ∨ lab (le s') < lab s ∨ lab (le s) < lab s')
    (P : ℝ → ℝ) (hP : Continuous P) (R : Finset ℝ) (hR : ∀ x, P x = 0 → x ∈ R)
    (hRd : R.card ≤ d)
    (al : ℕ → ℝ) (ha : ∀ s, |al (lab s)| ≤ 1)
    (has : ∀ s, P (lab s) ≠ 0 → al (lab s) = Real.sign (P (lab s))) (e : Bool)
    (u v : Fin b) (huv : u ≠ v) (E : Fin B ≃ {x : Fin b // x ≠ u ∧ x ≠ v})
    (rk : Fin B ≃ Fin B) (ρ : Fin B → Fin B) (hρ : Function.Involutive ρ) (hρ0 : ∀ r, ρ r ≠ r)
    (hρN : ∀ r, N ≤ r.val → N ≤ (ρ r).val)
    (hNc : (univ.filter (fun r : Fin B => N ≤ r.val)).card ≤ 2 * g)
    (hpair : ∀ r : Fin B, r.val < N → 0 ≤ Dfun loc w col lab al (E (rk.symm r)).1 +
      Dfun loc w col lab al (E (rk.symm (ρ r))).1) :
    ∃ (newM : Finset σ) (π : Fin b → Fin b),
      Function.Involutive π ∧ (∀ x, π x ≠ x) ∧ π u = v ∧
      newM ⊆ keepSet col lab P e ∧ newM.card ≤ 4 * d + (2 * g + 2) ∧
      ∀ x, (∑ s ∈ keepSet col lab P e,
          if s ∉ newM ∧ (loc s = x ∨ loc s = π x) then w s else 0) ≤ (T x + T (π x)) / 2 := by
  classical
  set keep := keepSet col lab P e with hkeep
  have hkc : ∀ s, s ∈ keep ↔ ce s ∉ keep := keep_ce ce col lab P e hcce hlce
  have hkp : ∀ s ∈ keep, P (lab s) ≠ 0 → sgnB (col s) * P (lab s) < 0 :=
    fun s hs => ((mem_keepSet _ _ _ _ _).1 hs).1
  set Z := keep.filter (fun s => P (lab s) = 0) with hZdef
  set L := Lset keep le w lab P with hLdef
  have hZc : Z.card ≤ d := (card_Z ce lab P keep hkc hlu R hR).trans hRd
  have hLc : L.card ≤ 3 * d :=
    (card_L ce le w col lab P hP e hle hcle hlu hclose R hR).trans (by omega)
  set K := keep \ (Z ∪ L) with hKdef
  have hKp : ∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0 := by
    intro s hs hls hsK
    by_contra hcon
    push Not at hcon
    have hs0 : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm hcon.1)
    have hs1 : 0 < w (le s) := lt_of_le_of_ne (hw _) (Ne.symm hcon.2)
    rw [hKdef, mem_sdiff, mem_union, not_or] at hs hsK
    have hP1 : P (lab s) ≠ 0 := fun h => hs.2.1 (mem_filter.2 ⟨hs.1, h⟩)
    have hP2 : P (lab (le s)) ≠ 0 := fun h => hsK.2.1 (mem_filter.2 ⟨hsK.1, h⟩)
    have hlab : lab s ≠ lab (le s) := by
      intro h
      rcases hlu s (le s) h with h' | h'
      · exact hls h'
      · exact (hkc s).1 hs.1 (h' ▸ hsK.1)
    rcases lt_or_gt_of_ne hlab with h | h
    · apply hsK.2.2
      rw [hLdef, mem_Lset, hle s]
      exact ⟨hsK.1, hP2, hs1, fun h' => hls h'.symm, hs.1, hP1, hs0, h⟩
    · apply hs.2.2
      rw [hLdef, mem_Lset]
      exact ⟨hs.1, hP1, hs0, hls, hsK.1, hP2, hs1, h⟩
  choose M hMK hM1 hMloc hMb using hK K hKp
  set U : Finset (Fin b) := {u, v} ∪
    (univ.filter (fun r : Fin B => N ≤ r.val)).image (fun r => (E (rk.symm r)).1) with hUdef
  have hUc : U.card ≤ 2 * g + 2 := by
    calc U.card ≤ ({u, v} : Finset (Fin b)).card +
          ((univ.filter (fun r : Fin B => N ≤ r.val)).image (fun r => (E (rk.symm r)).1)).card :=
          card_union_le _ _
      _ ≤ 2 + (univ.filter (fun r : Fin B => N ≤ r.val)).card :=
          Nat.add_le_add card_le_two card_image_le
      _ ≤ 2 * g + 2 := by omega
  set newM := Z ∪ L ∪ U.biUnion M with hnewM
  obtain ⟨π, hπ, hπ0, hπu, hπv, hπE⟩ := pairing_ext u v huv E (fun i => rk.symm (ρ (rk i)))
    (by intro i; simp only [Equiv.apply_symm_apply, hρ (rk i), Equiv.symm_apply_apply])
    (by
      intro i h
      apply hρ0 (rk i)
      have := congrArg rk h
      simpa using this)
  have hsubK : ∀ y ∈ U, ∀ s ∈ keep, s ∉ newM → s ∈ K ∧ s ∉ M y := by
    intro y hy s hs hsn
    rw [hnewM, mem_union, mem_union, not_or, not_or] at hsn
    refine ⟨mem_sdiff.2 ⟨hs, ?_⟩, fun h => hsn.2 (mem_biUnion.2 ⟨y, hy, h⟩)⟩
    rw [mem_union, not_or]; exact hsn.1
  have hbinU : ∀ y ∈ U, (∑ s ∈ keep, if s ∉ newM ∧ loc s = y then w s else 0) ≤ T y / 2 := by
    intro y hy
    exact bin_U loc w hw keep newM K (M y) y (hsubK y hy) (T y / 2)
      ((hMb y).trans (by linarith [hW y]))
  have hbinM : ∀ y, (∑ s ∈ keep, if s ∉ newM ∧ loc s = y then w s else 0) ≤
      ((∑ s ∈ univ.filter (fun s => loc s = y), w s) - Dfun loc w col lab al y) / 2 := by
    intro y
    refine bin_main loc w hw col lab P al ha has keep newM hkp ?_ y
    intro s hs hsn h
    apply hsn
    rw [hnewM, mem_union, mem_union]
    exact Or.inl (Or.inl (mem_filter.2 ⟨hs, h⟩))
  have huU : u ∈ U := mem_union_left _ (by simp)
  have hvU : v ∈ U := mem_union_left _ (by simp)
  refine ⟨newM, π, hπ, hπ0, hπu, ?_, ?_, ?_⟩
  · intro s hs
    rw [hnewM, mem_union, mem_union, mem_biUnion] at hs
    rcases hs with (h | h) | ⟨x, _, h⟩
    · exact (mem_filter.1 h).1
    · exact ((mem_Lset _ _ _ _ _ _).1 h).1
    · exact (mem_sdiff.1 (hMK x h)).1
  · calc newM.card ≤ (Z ∪ L).card + (U.biUnion M).card := card_union_le _ _
      _ ≤ Z.card + L.card + ∑ x ∈ U, (M x).card :=
          Nat.add_le_add (card_union_le _ _) card_biUnion_le
      _ ≤ d + 3 * d + ∑ x ∈ U, 1 := Nat.add_le_add (Nat.add_le_add hZc hLc)
          (sum_le_sum (fun x _ => hM1 x))
      _ ≤ 4 * d + (2 * g + 2) := by simp only [sum_const, smul_eq_mul, mul_one]; omega
  · intro x
    rw [pair_split _ _ _ _ (hπ0 x).symm]
    have hU2 : ∀ y z, y ∈ U → z ∈ U →
        (∑ s ∈ keep, if s ∉ newM ∧ loc s = y then w s else 0) +
          (∑ s ∈ keep, if s ∉ newM ∧ loc s = z then w s else 0) ≤ (T y + T z) / 2 := by
      intro y z hy hz
      linarith [hbinU y hy, hbinU z hz]
    rcases E_cases E x with rfl | rfl | ⟨i, rfl⟩
    · rw [hπu]; exact hU2 _ _ huU hvU
    · rw [hπv]; exact hU2 _ _ hvU huU
    · rw [hπE]
      by_cases hr : N ≤ (rk i).val
      · apply hU2
        · refine mem_union_right _ (mem_image.2 ⟨rk i, by simp [hr], by simp⟩)
        · exact mem_union_right _ (mem_image.2 ⟨ρ (rk i), by simp [hρN _ hr], rfl⟩)
      · have h := hpair (rk i) (by omega)
        simp only [Equiv.symm_apply_apply] at h
        have h1 := hbinM (E i).1
        have h2 := hbinM (E (rk.symm (ρ (rk i)))).1
        linarith [hW (E i).1, hW (E (rk.symm (ρ (rk i)))).1]

theorem main2 {σ : Type} [Fintype σ] [DecidableEq σ] {b B d : ℕ}
    (loc : σ → Fin b) (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (T : Fin b → ℝ)
    (hW : ∀ v, ∑ s ∈ univ.filter (fun s => loc s = v), w s ≤ T v)
    (ce le : σ → σ) (hle : Function.Involutive le)
    (hK : ∀ K : Finset σ, (∀ s ∈ K, le s ≠ s → le s ∈ K → w s = 0 ∨ w (le s) = 0) →
        ∀ v : Fin b, ∃ M : Finset σ, M ⊆ K ∧ M.card ≤ 1 ∧ (∀ s ∈ M, loc s = v) ∧
          (∑ s ∈ K, if loc s = v ∧ s ∉ M then w s else 0) ≤
            (∑ s ∈ univ.filter (fun s => loc s = v), w s) / 2)
    (col : σ → Bool) (lab : σ → ℕ)
    (hcce : ∀ s, col (ce s) ≠ col s) (hcle : ∀ s, le s ≠ s → col (le s) ≠ col s)
    (hlce : ∀ s, lab (ce s) = lab s) (hlu : ∀ s s', lab s = lab s' → s' = s ∨ s' = ce s)
    (hclose : ∀ s s', le s ≠ s → le s' ≠ s' → lab s + 2 ≤ lab (le s) →
      lab s' + 2 ≤ lab (le s') → s' = s ∨ lab (le s') < lab s ∨ lab (le s) < lab s')
    (P : ℝ → ℝ) (hP : Continuous P) (R : Finset ℝ) (hR : ∀ x, P x = 0 → x ∈ R)
    (hRd : R.card ≤ d)
    (al : ℕ → ℝ) (ha : ∀ s, |al (lab s)| ≤ 1)
    (has : ∀ s, P (lab s) ≠ 0 → al (lab s) = Real.sign (P (lab s))) (e : Bool)
    (u v : Fin b) (huv : u ≠ v) (E : Fin B ≃ {x : Fin b // x ≠ u ∧ x ≠ v})
    (rk : Fin B ≃ Fin B) (b' g : ℕ) (hB : B = 2 * b') (hg : 1 ≤ g) (hgb : g ≤ b')
    (hgd : b' < g * d)
    (hY : ∀ i j : Fin B, i ≤ j → Dfun loc w col lab al (E (rk.symm j)).1 ≤
      Dfun loc w col lab al (E (rk.symm i)).1)
    (hk : ∀ a : Fin d, ∀ i j : Fin B, i.val + 1 = min b' ((a.val + 1) * g) →
      j.val + min b' ((a.val + 1) * g) = B →
      Dfun loc w col lab al (E (rk.symm i)).1 + Dfun loc w col lab al (E (rk.symm j)).1 = 0) :
    ∃ (newM : Finset σ) (π : Fin b → Fin b),
      Function.Involutive π ∧ (∀ x, π x ≠ x) ∧ π u = v ∧
      newM ⊆ keepSet col lab P e ∧ newM.card ≤ 4 * d + (2 * g + 2) ∧
      ∀ x, (∑ s ∈ keepSet col lab P e,
          if s ∉ newM ∧ (loc s = x ∨ loc s = π x) then w s else 0) ≤ (T x + T (π x)) / 2 := by
  obtain ⟨ρ, hρ, hρ0, hρN, hρk⟩ := rank_pairing B b' g d hB hg hgb hgd
  refine main loc w hw T hW ce le hle hK col lab hcce hcle hlce hlu hclose P hP R hR hRd al ha
    has e u v huv E rk ρ hρ hρ0 hρN (by have := card_top B (B - 2 * g); omega) ?_
  intro r hr
  obtain ⟨a, h | h⟩ := hρk r hr
  · exact pair_from_rank (fun j => Dfun loc w col lab al (E (rk.symm j)).1) hY
      (fun a => min b' ((a.val + 1) * g)) hk r (ρ r) a h.1 h.2
  · have := pair_from_rank (fun j => Dfun loc w col lab al (E (rk.symm j)).1) hY
      (fun a => min b' ((a.val + 1) * g)) hk (ρ r) r a h.1 h.2
    linarith

lemma finish {σ : Type} [Fintype σ] [DecidableEq σ] {b d g : ℕ} (loc : σ → Fin b)
    (w : σ → ℝ) (T : Fin b → ℝ) (ce : σ → σ) (keep : Finset σ)
    (hkc : ∀ s, s ∈ keep ↔ ce s ∉ keep) (X : Finset (Fin b)) (u₀ v₀ u v : Fin b)
    (huvX : X ≠ ∅ → u = u₀ ∧ v = v₀) (Old : Finset σ) (hOld : 2 * (Old ∩ keep).card ≤ Old.card)
    (hcount : 4 * d + (2 * g + 2) ≤ 6 * Nat.sqrt b)
    (h : ∃ (newM : Finset σ) (π : Fin b → Fin b),
      Function.Involutive π ∧ (∀ x, π x ≠ x) ∧ π u = v ∧
      newM ⊆ keep ∧ newM.card ≤ 4 * d + (2 * g + 2) ∧
      ∀ x, (∑ s ∈ keep, if s ∉ newM ∧ (loc s = x ∨ loc s = π x) then w s else 0) ≤
        (T x + T (π x)) / 2) :
    ∃ (keep newM : Finset σ) (π : Fin b → Fin b),
      (∀ s, s ∈ keep ↔ ce s ∉ keep) ∧
      Function.Involutive π ∧ (∀ v, π v ≠ v) ∧ (X ≠ ∅ → π u₀ = v₀) ∧
      newM ⊆ keep ∧ 2 * (Old ∩ keep).card ≤ Old.card ∧
      (newM.card : ℝ) ≤ 6 * Real.sqrt b ∧
      ∀ v, (∑ s ∈ keep, if s ∉ newM ∧ (loc s = v ∨ loc s = π v) then w s else 0) ≤
        (T v + T (π v)) / 2 := by
  obtain ⟨newM, π, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨keep, newM, π, hkc, h1, h2, fun hX => ?_, h4, hOld, ?_, h6⟩
  · obtain ⟨rfl, rfl⟩ := huvX hX; exact h3
  · have h7 : (newM.card : ℝ) ≤ 6 * (Nat.sqrt b : ℝ) := by exact_mod_cast h5.trans hcount
    have h8 := Real.nat_sqrt_le_real_sqrt (a := b)
    linarith

lemma A_sum {σ : Type} [Fintype σ] [DecidableEq σ] {b Tn : ℕ} (loc : σ → Fin b) (w : σ → ℝ)
    (col : σ → Bool) (lab : σ → ℕ) (hlab : ∀ s, lab s < Tn) (α : Fin Tn → ℝ) (x : Fin b) :
    ∑ t : Fin Tn, (∑ s, if loc s = x ∧ lab s = t.val then w s * sgnB (col s) else 0) * α t =
      Dfun loc w col lab (fun n => if h : n < Tn then α ⟨n, h⟩ else 0) x := by
  simp_rw [sum_mul]
  rw [sum_comm]
  unfold Dfun
  rw [sum_filter]
  refine sum_congr rfl (fun s _ => ?_)
  by_cases hl : loc s = x
  · rw [if_pos hl, sum_eq_single ⟨lab s, hlab s⟩]
    · simp [hl, hlab s]
    · intro t _ ht
      rw [if_neg]
      · simp
      rintro ⟨_, h⟩; exact ht (Fin.ext h.symm)
    · simp
  · rw [if_neg hl]; simp [hl]

theorem core : ∃ b₀ : ℕ, ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (b : ℕ), b₀ ≤ b → Even b →
    ∀ (loc : σ → Fin b) (w : σ → ℝ), (∀ s, 0 ≤ w s) →
    ∀ (T : Fin b → ℝ), (∀ v, 0 ≤ T v) →
    (∀ v, ∑ s ∈ univ.filter (fun s => loc s = v), w s ≤ T v) →
    ∀ (ce : σ → σ), Function.Involutive ce → (∀ s, ce s ≠ s) →
    ∀ (X : Finset (Fin b)) (u₀ v₀ : Fin b), (X = ∅ ∨ (X = {u₀, v₀} ∧ u₀ ≠ v₀)) →
    (∀ v, v ∉ X → T v = 1) →
    ∀ (Old : Finset σ), (∀ s ∈ Old, w s = 0) →
    ∃ (keep newM : Finset σ) (π : Fin b → Fin b),
      (∀ s, s ∈ keep ↔ ce s ∉ keep) ∧
      Function.Involutive π ∧ (∀ v, π v ≠ v) ∧ (X ≠ ∅ → π u₀ = v₀) ∧
      newM ⊆ keep ∧ 2 * (Old ∩ keep).card ≤ Old.card ∧
      (newM.card : ℝ) ≤ 6 * Real.sqrt b ∧
      ∀ v, (∑ s ∈ keep, if s ∉ newM ∧ (loc s = v ∨ loc s = π v) then w s else 0) ≤
        (T v + T (π v)) / 2 := by
  refine ⟨400, ?_⟩
  intro σ _ _ b hb hbe loc w hw T _ hW ce hce hce0 X u₀ v₀ hX _ Old _
  classical
  obtain ⟨u, v, huv, huvX⟩ : ∃ u v : Fin b, u ≠ v ∧ (X ≠ ∅ → u = u₀ ∧ v = v₀) := by
    rcases hX with hX | ⟨-, hne⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], fun h => absurd hX h⟩
    · exact ⟨u₀, v₀, hne, fun _ => ⟨rfl, rfl⟩⟩
  obtain ⟨r0, hr0⟩ := hbe
  -- numeric parameters
  obtain ⟨bh, hbh⟩ : ∃ bh, bh = r0 - 1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = b - 2 := ⟨_, rfl⟩
  have hB : B = 2 * bh := by omega
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = s + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = bh / d := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = q + 1 := ⟨_, rfl⟩
  have hs20 : 20 ≤ s := by rw [hs]; exact Nat.le_sqrt.2 (by omega)
  have hbd : b < d * d := by
    have := Nat.lt_succ_sqrt' b
    rw [← hs, Nat.succ_eq_add_one, ← hd, pow_two] at this; exact this
  have hqd : q * d ≤ bh := by rw [hq]; exact Nat.div_mul_le_self bh d
  have hgd : bh < g * d := by
    have := Nat.lt_div_mul_add (a := bh) (b := d) (by omega)
    have e1 : g * d = q * d + d := by rw [hgdef]; ring
    rw [← hq] at this
    omega
  have hgb : g ≤ bh := by
    have : q * 21 ≤ q * d := Nat.mul_le_mul_left q (by omega)
    omega
  have hcount : 4 * d + (2 * g + 2) ≤ 6 * Nat.sqrt b := by
    have h2 : (2 * q) * d < d * d := by
      have e1 : (2 * q) * d = 2 * (q * d) := by ring
      omega
    have := Nat.lt_of_mul_lt_mul_right h2
    rw [← hs]
    omega
  -- the unit bins
  have hcardE : Fintype.card {x : Fin b // x ≠ u ∧ x ≠ v} = B := by
    rw [Fintype.card_subtype]
    have : (univ.filter (fun x : Fin b => x ≠ u ∧ x ≠ v)) = univ \ {u, v} := by
      ext x; simp
    rw [this, card_univ_sdiff, Fintype.card_fin, card_pair huv]
    omega
  let E : Fin B ≃ {x : Fin b // x ≠ u ∧ x ≠ v} := (Fintype.equivFinOfCardEq hcardE).symm
  -- local-edges and the graph structure
  obtain ⟨le, hle, -, hK⟩ := local_edges loc w hw
  obtain ⟨col, lab, hcce, hcle, hlce, hlu, hlab2, hclose⟩ := graph_structure ce le hce hce0 hle
  have hlabT : ∀ s, lab s < Fintype.card σ := fun s => by have := hlab2 s; omega
  -- Step 1
  let A : Fin B → Fin (Fintype.card σ) → ℝ := fun i t =>
    ∑ s, if loc s = (E i).1 ∧ lab s = t.val then w s * sgnB (col s) else 0
  let k : Fin d → ℕ := fun a => min bh ((a.val + 1) * g)
  have hk : ∀ a, 1 ≤ k a ∧ k a ≤ B := by
    intro a
    have : 1 ≤ (a.val + 1) * g := Nat.mul_pos (by omega) (by omega)
    exact ⟨le_min (by omega) this, (min_le_left _ _).trans (by omega)⟩
  obtain ⟨z, hz, α, hα1, hαs, hostat⟩ := step1 A k hk
  obtain ⟨rk, hrk1, hrk2⟩ := ostat_sorted (fun i => ∑ t, A i t * α t)
  let αN : ℕ → ℝ := fun n => if h : n < Fintype.card σ then α ⟨n, h⟩ else 0
  have hAD : ∀ i, (∑ t, A i t * α t) = Dfun loc w col lab αN (E i).1 :=
    fun i => A_sum loc w col lab hlabT α (E i).1
  obtain ⟨R, hRd, hR⟩ := poly_roots z hz
  have hY : ∀ i j : Fin B, i ≤ j → Dfun loc w col lab αN (E (rk.symm j)).1 ≤
      Dfun loc w col lab αN (E (rk.symm i)).1 := by
    intro i j hij; rw [← hAD, ← hAD]; exact hrk2 i j hij
  have hkk : ∀ a : Fin d, ∀ i j : Fin B, i.val + 1 = min bh ((a.val + 1) * g) →
      j.val + min bh ((a.val + 1) * g) = B →
      Dfun loc w col lab αN (E (rk.symm i)).1 + Dfun loc w col lab αN (E (rk.symm j)).1 = 0 := by
    intro a i j hi hj
    have h1 : Dfun loc w col lab αN (E (rk.symm i)).1 =
        ostat (k a) (fun v => ∑ t, A v t * α t) := by
      rw [← hAD]; rw [show k a = i.val + 1 from hi.symm]; exact hrk1 i
    have h2 : Dfun loc w col lab αN (E (rk.symm j)).1 =
        ostat (B + 1 - k a) (fun v => ∑ t, A v t * α t) := by
      rw [← hAD]; rw [show B + 1 - k a = j.val + 1 by simp only [k]; omega]; exact hrk1 j
    rw [h1, h2]; exact hostat a
  have ha : ∀ s, |αN (lab s)| ≤ 1 := by
    intro s
    simp only [αN, dif_pos (hlabT s)]
    exact abs_le.2 ⟨(hα1 _).1, (hα1 _).2⟩
  have has : ∀ s, polyEval z (lab s) ≠ 0 → αN (lab s) = Real.sign (polyEval z (lab s)) := by
    intro s h
    simp only [αN, dif_pos (hlabT s)]
    exact hαs ⟨lab s, hlabT s⟩ h
  -- the two orientations
  have hcompl := keep_compl col lab (polyEval z)
  have hsum : (Old ∩ keepSet col lab (polyEval z) true).card +
      (Old ∩ keepSet col lab (fun x => -polyEval z x) false).card = Old.card := by
    have e1 : Old ∩ keepSet col lab (polyEval z) true =
        Old.filter (fun s => s ∈ keepSet col lab (polyEval z) true) := by
      ext s; simp
    have e2 : Old ∩ keepSet col lab (fun x => -polyEval z x) false =
        Old.filter (fun s => ¬ s ∈ keepSet col lab (polyEval z) true) := by
      ext s; simp only [mem_inter, mem_filter, hcompl s, not_not]
    rw [e1, e2]; exact card_filter_add_card_filter_not _
  by_cases hO : 2 * (Old ∩ keepSet col lab (polyEval z) true).card ≤ Old.card
  · refine finish loc w T ce _ (keep_ce ce col lab _ true hcce hlce) X u₀ v₀ u v huvX Old hO
      hcount ?_
    exact main2 loc w hw T hW ce le hle hK col lab hcce hcle hlce hlu hclose (polyEval z)
      (polyEval_continuous z) R hR hRd αN ha has true u v huv E rk bh g hB (by omega) hgb hgd
      hY hkk
  · have hO' : 2 * (Old ∩ keepSet col lab (fun x => -polyEval z x) false).card ≤ Old.card := by
      omega
    refine finish loc w T ce _ (keep_ce ce col lab _ false hcce hlce) X u₀ v₀ u v huvX Old hO'
      hcount ?_
    have hrev : ∀ j : Fin B, (rk.trans Fin.revPerm).symm j = rk.symm (Fin.rev j) := by
      intro j; rfl
    refine main2 loc w hw T hW ce le hle hK col lab hcce hcle hlce hlu hclose
      (fun x => -polyEval z x) (polyEval_continuous z).neg R (fun x hx => hR x (by linarith))
      hRd (fun n => -αN n) (fun s => by rw [abs_neg]; exact ha s) ?_ false u v huv E
      (rk.trans Fin.revPerm) bh g hB (by omega) hgb hgd ?_ ?_
    · intro s h
      rw [Real.sign_neg, has s (fun h' => h (by rw [h']; simp))]
    · intro i j hij
      rw [Dfun_neg, Dfun_neg, hrev, hrev, neg_le_neg_iff]
      apply hY
      rw [Fin.le_def, Fin.val_rev, Fin.val_rev]
      rw [Fin.le_def] at hij
      omega
    · intro a i j hi hj
      rw [Dfun_neg, Dfun_neg, hrev, hrev]
      have := hkk a (Fin.rev j) (Fin.rev i) (by rw [Fin.val_rev]; omega)
        (by rw [Fin.val_rev]; omega)
      linarith

end SublinearChoresMMS.Disposal.Dev.LA2.PartC
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part C: the abstract halving step (Steps 1–3 of the proof of Lemma A.2) -/
alias core := SublinearChoresMMS.Disposal.Dev.LA2.PartC.core

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2.PartB
open SublinearChoresMMS.Disposal
open Finset
/-- Flip the last bit of the copy index (`k ↦ k xor 1`). -/
def flipCopy {α : Type} {N : ℕ} (hN : N % 2 = 0) (s : α × Fin N) : α × Fin N :=
  (s.1, ⟨if s.2.val % 2 = 0 then s.2.val + 1 else s.2.val - 1, by
    have := s.2.isLt
    split_ifs <;> omega⟩)

lemma flipCopy_fst {α : Type} {N : ℕ} (hN : N % 2 = 0) (s : α × Fin N) :
    (flipCopy hN s).1 = s.1 := rfl

lemma flipCopy_invol {α : Type} {N : ℕ} (hN : N % 2 = 0) :
    Function.Involutive (flipCopy (α := α) hN) := by
  intro s
  obtain ⟨a, k⟩ := s
  simp only [flipCopy]
  ext
  · rfl
  · simp only
    split_ifs <;> omega

lemma flipCopy_ne {α : Type} {N : ℕ} (hN : N % 2 = 0) (s : α × Fin N) :
    flipCopy hN s ≠ s := by
  obtain ⟨a, k⟩ := s
  intro h
  have := congrArg (fun x => x.2.val) h
  simp only [flipCopy] at this
  split_ifs at this <;> omega

lemma row_card {α : Type} [Fintype α] [DecidableEq α] {N : ℕ} (hN : N % 2 = 0)
    (keep : Finset (α × Fin N)) (hk : ∀ s, s ∈ keep ↔ flipCopy hN s ∉ keep) (r : α) :
    (keep.filter (fun s => s.1 = r)).card = N / 2 := by
  set K := keep.filter (fun s => s.1 = r) with hK
  have hR : (univ.filter (fun s : α × Fin N => s.1 = r)) = K ∪ K.image (flipCopy hN) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, hK]
    constructor
    · intro hs
      by_cases h : s ∈ keep
      · exact Or.inl ⟨h, hs⟩
      · right
        refine ⟨flipCopy hN s, ⟨?_, ?_⟩, flipCopy_invol hN s⟩
        · by_contra h'
          exact h ((hk s).2 h')
        · rw [flipCopy_fst]; exact hs
    · rintro (⟨_, hs⟩ | ⟨t, ⟨_, ht⟩, rfl⟩)
      · exact hs
      · rw [flipCopy_fst]; exact ht
  have hdisj : Disjoint K (K.image (flipCopy hN)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hs'
    have ht1 := (mem_filter.1 ht).1
    have hs1 := (mem_filter.1 hs).1
    exact ((hk t).1 ht1) hs1
  have hcardR : (univ.filter (fun s : α × Fin N => s.1 = r)).card = N := by
    have : (univ.filter (fun s : α × Fin N => s.1 = r)) =
        (univ : Finset (Fin N)).map ⟨fun k => (r, k), fun a b h => by
          simpa using h⟩ := by
      ext s
      obtain ⟨a, k⟩ := s
      simp only [mem_filter, mem_univ, true_and, mem_map]
      constructor
      · rintro rfl; exact ⟨k, rfl⟩
      · rintro ⟨k', h⟩; exact (congrArg Prod.fst h).symm
    rw [this, card_map, card_univ, Fintype.card_fin]
  rw [hR, card_union_of_disjoint hdisj,
    card_image_of_injective _ (flipCopy_invol hN).injective] at hcardR
  omega

/-- The exceptional set and pair for the halving stage. -/
lemma exc_data (n j : ℕ) (hb : 2 ≤ stageBins n j) :
    ∃ (X : Finset (Fin (stageBins n j))) (u₀ v₀ : Fin (stageBins n j)),
      (X = ∅ ∨ (X = {u₀, v₀} ∧ u₀ ≠ v₀)) ∧
      (∀ v, v ∉ X → stageCapacity n j v = 1) ∧
      (∀ u v, ExceptionalPair n j u v → X ≠ ∅ ∧ u = u₀ ∧ v = v₀) := by
  have hsb : stageBins n j = binCount n (2 ^ j) + binCount n (2 ^ j) % 2 := rfl
  have hbc : binCount n (2 ^ j) = n / 2 ^ j + if n % 2 ^ j = 0 then 0 else 1 := rfl
  have hcap : ∀ v : Fin (stageBins n j), v.val < n / 2 ^ j → stageCapacity n j v = 1 := by
    intro v hv
    simp [stageCapacity, hv]
  by_cases ha : (n / 2 ^ j) % 2 = 0
  · by_cases hr : n % 2 ^ j = 0
    · rw [hr, if_pos rfl] at hbc
      refine ⟨∅, ⟨0, by omega⟩, ⟨0, by omega⟩, Or.inl rfl, ?_, ?_⟩
      · intro v _
        apply hcap
        have := v.isLt
        omega
      · intro u v h
        simp [ExceptionalPair, ha, hr] at h
    · rw [if_neg hr] at hbc
      have hS : stageBins n j = n / 2 ^ j + 2 := by omega
      refine ⟨{⟨n / 2 ^ j, by omega⟩, ⟨n / 2 ^ j + 1, by omega⟩},
        ⟨n / 2 ^ j, by omega⟩, ⟨n / 2 ^ j + 1, by omega⟩,
        Or.inr ⟨rfl, by simp [Fin.ext_iff]⟩, ?_, ?_⟩
      · intro v hv
        apply hcap
        simp only [mem_insert, mem_singleton, not_or, Fin.ext_iff] at hv
        have := v.isLt
        omega
      · intro u v h
        simp only [ExceptionalPair, ha, if_true] at h
        obtain ⟨_, hu, hv⟩ := h
        refine ⟨by simp, Fin.ext hu, Fin.ext hv⟩
  · have hS : stageBins n j = n / 2 ^ j + 1 := by
      split_ifs at hbc <;> omega
    refine ⟨{⟨0, by omega⟩, ⟨n / 2 ^ j, by omega⟩},
      ⟨0, by omega⟩, ⟨n / 2 ^ j, by omega⟩,
      Or.inr ⟨rfl, by simp only [ne_eq, Fin.ext_iff]; omega⟩, ?_, ?_⟩
    · intro v hv
      apply hcap
      simp only [mem_insert, mem_singleton, not_or, Fin.ext_iff] at hv
      have := v.isLt
      omega
    · intro u v h
      simp only [ExceptionalPair, ha, if_false] at h
      obtain ⟨hu, hv⟩ := h
      refine ⟨by simp, Fin.ext hu, Fin.ext hv⟩

theorem lemma_a_2 :
    ∃ C₃ : ℝ, 5 < C₃ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n m ℓ j : ℕ), j < ℓ → 0 < n → 0 < m →
        2 ^ ℓ ∣ m → b₀ ≤ stageBins n j →
        ∀ (c : Cost n m), Normalized c → ∀ (i : Fin n)
          (P : CopyPacking n m (2 ^ ℓ) j),
          CopyFeasible c i P →
          (P.marked.card : ℝ) ≤ 8 * C₃ * Real.sqrt ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) →
          HalvingOutput c i P C₃ := by
  obtain ⟨b₀, hcore⟩ := SublinearChoresMMS.Disposal.Dev.LA2.core
  refine ⟨6, by norm_num, max b₀ 2, le_max_right _ _, ?_⟩
  intro n m ℓ j hjl _ _ _ hb c hc i P hfeas _
  classical
  have hN : (2 ^ ℓ / 2 ^ j) % 2 = 0 := by
    rw [Nat.pow_div hjl.le (by norm_num)]
    obtain ⟨k, hk⟩ : ∃ k, ℓ - j = k + 1 := ⟨ℓ - j - 1, by omega⟩
    rw [hk, pow_succ]
    simp
  have hb2 : 2 ≤ stageBins n j := le_trans (le_max_right _ _) hb
  have hev : Even (stageBins n j) := by
    rw [Nat.even_iff]
    show (binCount n (2 ^ j) + binCount n (2 ^ j) % 2) % 2 = 0
    omega
  obtain ⟨X, u₀, v₀, hX, hT1, hexc⟩ := exc_data n j hb2
  let w : Copies m (2 ^ ℓ) j → ℝ := fun s =>
    if s ∈ P.marked then 0 else representativeCost c i (2 ^ ℓ) s.1.val
  have hw : ∀ s, 0 ≤ w s := by
    intro s
    simp only [w]
    split_ifs
    · exact le_rfl
    · unfold representativeCost
      split_ifs
      · exact (hc.1 _ _).le
      · exact le_rfl
  have hT : ∀ v, 0 ≤ stageCapacity n j v := by
    intro v
    unfold stageCapacity
    split_ifs <;> positivity
  have hload : ∀ v, ∑ s ∈ univ.filter (fun s => P.location s = v), w s ≤
      stageCapacity n j v := by
    intro v
    refine le_trans (le_of_eq ?_) (hfeas.1 v)
    rw [sum_filter]
    unfold copyLoad
    refine sum_congr rfl fun s _ => ?_
    by_cases h1 : P.location s = v <;> by_cases h2 : s ∈ P.marked <;> simp [w, h1, h2]
  have hOld : ∀ s ∈ P.marked, w s = 0 := by
    intro s hs
    simp [w, hs]
  obtain ⟨keep, newM, π, hk, hπi, hπn, hπX, hsub, hOldc, hcard, hloadc⟩ :=
    hcore (stageBins n j) (le_trans (le_max_left _ _) hb) hev P.location w hw
      (stageCapacity n j) hT hload (flipCopy hN) (flipCopy_invol hN) (flipCopy_ne hN)
      X u₀ v₀ hX hT1 P.marked hOld
  refine ⟨keep, newM ∪ (P.marked ∩ keep), π, ⟨hπi, hπn⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    obtain ⟨hXne, rfl, rfl⟩ := hexc u v h
    exact hπX hXne
  · intro r
    exact row_card hN keep hk r
  · exact union_subset hsub inter_subset_right
  · exact subset_union_right
  · intro v
    refine le_trans (sum_le_sum fun s hs => ?_) (hloadc v)
    by_cases h1 : s ∈ newM ∪ (P.marked ∩ keep)
    · rw [if_neg (fun h => h.1 h1)]
      split_ifs
      · exact hw s
      · exact le_rfl
    · have hs1 : s ∉ newM := fun h => h1 (mem_union_left _ h)
      have hs2 : s ∉ P.marked := fun h => h1 (mem_union_right _ (mem_inter.2 ⟨h, hs⟩))
      by_cases hl : (P.location s = v ∨ P.location s = π v)
      · rw [if_pos ⟨h1, hl⟩, if_pos ⟨hs1, hl⟩]
        simp [w, hs2]
      · rw [if_neg (fun h => hl h.2), if_neg (fun h => hl h.2)]
  · have h1 := card_union_le newM (P.marked ∩ keep)
    have h1' : ((newM ∪ (P.marked ∩ keep)).card : ℝ) ≤
        (newM.card : ℝ) + ((P.marked ∩ keep).card : ℝ) := by exact_mod_cast h1
    have h2 : (2 : ℝ) * ((P.marked ∩ keep).card : ℝ) ≤ (P.marked.card : ℝ) := by
      exact_mod_cast hOldc
    linarith

end SublinearChoresMMS.Disposal.Dev.LA2.PartB
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part B: the bundle's Lemma A.2 -/
alias lemma_a_2 := SublinearChoresMMS.Disposal.Dev.LA2.PartB.lemma_a_2

end SublinearChoresMMS.Disposal.Dev.LA2
end
end

section
noncomputable section
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev
open SublinearChoresMMS.Disposal.Dev.LA2
open SublinearChoresMMS.Disposal
open Finset
theorem solution :
    ∃ C₃ : ℝ, 5 < C₃ ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n m ℓ j : ℕ), j < ℓ → 0 < n → 0 < m →
        2 ^ ℓ ∣ m → b₀ ≤ stageBins n j →
        ∀ (c : Cost n m), Normalized c → ∀ (i : Fin n)
          (P : CopyPacking n m (2 ^ ℓ) j),
          CopyFeasible c i P →
          (P.marked.card : ℝ) ≤ 8 * C₃ * Real.sqrt ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) →
          HalvingOutput c i P C₃ := by
  exact SublinearChoresMMS.Disposal.Dev.LA2.lemma_a_2
end
end
