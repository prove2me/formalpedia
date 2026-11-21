-- Prove2me | solution 1 for RobustObedientPersuasion.Saddle.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:47:32.776175+00:00
-- url     : https://prove2.me/submissions/50b907d8-98c4-4664-a514-8ad41eb03483

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model
import Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted
universe v

section
namespace RobustObedientPersuasion.Saddle.Supplement.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma le_one_of_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∑ i, f i = 1) (i : ι) : f i ≤ 1 := by
  rw [← h1]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma pi_le_one {α : A → ℝ} {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α) (ω : Ω) (a : A) :
    π ω a ≤ 1 := le_one_of_sum (π ω) (hπ.1 ω) (hπ.2.1 ω) a

end

end RobustObedientPersuasion.Saddle.Supplement.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev

lemma fin_family {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] (K : Set X) (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : K.Nonempty)
    (g : ι → X → ℝ) (hg : ∀ i, Continuous (g i))
    (haff : ∀ i x1 x2 (a b : ℝ), a + b = 1 → g i (a • x1 + b • x2) = a * g i x1 + b * g i x2)
    (c : ℝ)
    (H : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → ∃ x ∈ K, c ≤ ∑ i, w i * g i x) :
    ∃ x ∈ K, ∀ i, c ≤ g i x := by
  classical
  by_contra hcon
  push_neg at hcon
  set T : Set (ι → ℝ) := (fun x i => g i x) '' K with hT
  have hTc : IsCompact T := hK.image (continuous_pi hg)
  have hTconv : Convex ℝ T := by
    rintro _ ⟨x1, hx1, rfl⟩ _ ⟨x2, hx2, rfl⟩ a b ha hb hab
    refine ⟨a • x1 + b • x2, hKc hx1 hx2 ha hb hab, ?_⟩
    ext i
    simp [haff i x1 x2 a b hab]
  set Q : Set (ι → ℝ) := {t | ∀ i, c ≤ t i} with hQ
  have hQc : IsClosed Q := by
    simp only [Q, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hQconv : Convex ℝ Q := by
    intro s hs t ht a b ha hb hab i
    have h1 := hs i
    have h2 := ht i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2)]
  have hdis : Disjoint T Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hq
    obtain ⟨i, hi⟩ := hcon x hx
    exact absurd (hq i) (not_le.mpr hi)
  obtain ⟨ℓ, u, v, hu, huv, hv⟩ := geometric_hahn_banach_compact_closed hTconv hTc hQconv hQc hdis
  set w : ι → ℝ := fun i => ℓ (fun j => if i = j then 1 else 0) with hwdef
  have hℓ : ∀ t : ι → ℝ, ℓ t = ∑ i, w i * t i := by
    intro t
    conv_lhs => rw [pi_eq_sum_univ t]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    by_contra hneg
    push_neg at hneg
    have hq : ∀ s : ℝ, 0 ≤ s → v < c * ∑ i, w i + s * w j := by
      intro s hs
      have := hv (fun i => c + if i = j then s else 0) (fun i => by show c ≤ c + if i = j then s else 0; split_ifs <;> linarith)
      rw [hℓ] at this
      have e : ∑ i, w i * (c + if i = j then s else 0) = c * ∑ i, w i + s * w j := by
        simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq', ← Finset.sum_mul]
        ring
      linarith
    have hs0 : 0 ≤ (|v| + |c * ∑ i, w i| + 1) / (-w j) :=
      div_nonneg (by positivity) (by linarith)
    have h := hq _ hs0
    have e2 : (|v| + |c * ∑ i, w i| + 1) / (-w j) * w j = -(|v| + |c * ∑ i, w i| + 1) := by
      have : w j ≠ 0 := hneg.ne
      field_simp
    rw [e2] at h
    linarith [neg_abs_le v, le_abs_self (c * ∑ i, w i)]
  have hWnn : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  rcases hWnn.eq_or_lt with h0 | hpos
  · have hz : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp h0.symm i (Finset.mem_univ i)
    obtain ⟨x0, hx0⟩ := hKn
    have h1 := hu _ ⟨x0, hx0, rfl⟩
    have h2 := hv (fun _ => c) (fun _ => le_rfl)
    rw [hℓ] at h1 h2
    simp [hz] at h1 h2
    linarith
  · obtain ⟨x, hx, hxc⟩ := H (fun i => w i / ∑ i, w i) (fun i => div_nonneg (hw i) hpos.le)
      (by rw [← Finset.sum_div]; exact div_self hpos.ne')
    have h1 := hu (fun i => g i x) ⟨x, hx, rfl⟩
    have h2 := hv (fun _ => c) (fun _ => le_rfl)
    rw [hℓ] at h1 h2
    have e1 : ∑ i, (w i / ∑ i, w i) * g i x = (∑ i, w i * g i x) / ∑ i, w i := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, le_div_iff₀ hpos] at hxc
    have e2 : ∑ i, w i * c = c * ∑ i, w i := by rw [← Finset.sum_mul, mul_comm]
    linarith

lemma minimax_exists {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y : Type v}
    [AddCommGroup Y] [Module ℝ Y]
    (K : Set X) (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : K.Nonempty) (L : Set Y)
    (hLc : Convex ℝ L) (f : X → Y → ℝ) (hcont : ∀ y, Continuous fun x => f x y)
    (haff : ∀ y x1 x2 (a b : ℝ), a + b = 1 → f (a • x1 + b • x2) y = a * f x1 y + b * f x2 y)
    (hlin : ∀ (ι : Type v) [Fintype ι] (lam : ι → ℝ) (y : ι → Y), ∑ i, lam i = 1 →
      ∀ x, f x (∑ i, lam i • y i) = ∑ i, lam i * f x (y i))
    (c : ℝ) (H : ∀ y ∈ L, ∃ x ∈ K, c ≤ f x y) : ∃ x ∈ K, ∀ y ∈ L, c ≤ f x y := by
  have := hK.inter_iInter_nonempty (fun y : L => {x | c ≤ f x y.1})
    (fun y => isClosed_le continuous_const (hcont y.1)) ?_
  · obtain ⟨x, hxK, hx⟩ := this
    exact ⟨x, hxK, fun y hy => Set.mem_iInter.mp hx ⟨y, hy⟩⟩
  · intro u
    have hfam : ∀ w : u → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        ∃ x ∈ K, c ≤ ∑ i, w i * (fun (i : u) (x : X) => f x i.1.1) i x := by
      intro w hw1 hw2
      have hmem : ∑ i : u, w i • (i.1.1 : Y) ∈ L :=
        hLc.sum_mem (fun i _ => hw1 i) hw2 (fun i _ => i.1.2)
      obtain ⟨x, hx, hxc⟩ := H _ hmem
      refine ⟨x, hx, ?_⟩
      rw [hlin u w (fun i => i.1.1) hw2] at hxc
      exact hxc
    obtain ⟨x, hx, hxc⟩ := fin_family (ι := u) K hK hKc hKn (fun i x => f x i.1.1)
      (fun i => hcont _) (fun i x1 x2 a b hab => haff _ _ _ a b hab) c hfam
    exact ⟨x, hx, Set.mem_iInter₂.mpr fun i hi => hxc ⟨i, hi⟩⟩

end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement RobustObedientPersuasion.Saddle.Supplement.Dev

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma obedienceRegion_isCompact (u : Ω → A → ℝ) (a : A) : IsCompact (obedienceRegion u a) := by
  refine (isCompact_stdSimplex ℝ Ω).of_isClosed_subset ?_ (fun ν hν => hν.1)
  have h1 : IsClosed (stdSimplex ℝ Ω) := (isCompact_stdSimplex ℝ Ω).isClosed
  have h2 : IsClosed {ν : Ω → ℝ | ∀ a' : A, 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} := by
    have : {ν : Ω → ℝ | ∀ a' : A, 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} =
        ⋂ a', {ν : Ω → ℝ | 0 ≤ ∑ ω, ν ω * (u ω a - u ω a')} := by ext; simp
    rw [this]
    exact isClosed_iInter fun a' => isClosed_le continuous_const
      (continuous_finset_sum _ fun ω _ => (continuous_apply ω).mul continuous_const)
  have h3 := h1.inter h2
  exact h3

lemma obedienceRegion_convex (u : Ω → A → ℝ) (a : A) : Convex ℝ (obedienceRegion u a) := by
  intro x hx y hy s t hs ht hst
  refine ⟨(convex_stdSimplex ℝ Ω) hx.1 hy.1 hs ht hst, fun a' => ?_⟩
  have h1 := hx.2 a'
  have h2 := hy.2 a'
  have : ∑ ω, (s • x + t • y) ω * (u ω a - u ω a') =
      s * ∑ ω, x ω * (u ω a - u ω a') + t * ∑ ω, y ω * (u ω a - u ω a') := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [this]
  exact add_nonneg (mul_nonneg hs h1) (mul_nonneg ht h2)

lemma identifiedSet_eq (u : Ω → A → ℝ) (α : A → ℝ) :
    identifiedSet u α = (fun ν : A → Ω → ℝ => fun ω => ∑ a ∈ supp α, α a * ν a ω) ''
      Set.pi Set.univ (fun a => {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧
        (a ∉ supp α → x = 0)}) := by
  classical
  ext μ
  constructor
  · rintro ⟨ν, hν, hμ⟩
    refine ⟨fun a => if a ∈ supp α then ν a else 0, ?_, ?_⟩
    · intro a _
      by_cases h : a ∈ supp α
      · simp [h, hν a h]
      · simp [h]
    · funext ω
      rw [hμ]
      exact Finset.sum_congr rfl fun a ha => by simp [ha]
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, fun a ha => (hν a (Set.mem_univ a)).1 ha, fun ω => rfl⟩

lemma ident_compact (u : Ω → A → ℝ) (α : A → ℝ) : IsCompact (identifiedSet u α) := by
  rw [identifiedSet_eq]
  refine (isCompact_univ_pi fun a => ?_).image ?_
  · by_cases h : a ∈ supp α
    · have : {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧ (a ∉ supp α → x = 0)} =
          obedienceRegion u a := by ext x; simp [h]
      rw [this]; exact obedienceRegion_isCompact u a
    · have : {x : Ω → ℝ | (a ∈ supp α → x ∈ obedienceRegion u a) ∧ (a ∉ supp α → x = 0)} =
          {0} := by ext x; simp [h]
      rw [this]; exact isCompact_singleton
  · exact continuous_pi fun ω => continuous_finset_sum _ fun a _ =>
      continuous_const.mul ((continuous_apply ω).comp (continuous_apply a))

lemma ident_convex (u : Ω → A → ℝ) (α : A → ℝ) : Convex ℝ (identifiedSet u α) := by
  rintro x ⟨νx, hνx, hx⟩ y ⟨νy, hνy, hy⟩ s t hs ht hst
  refine ⟨fun a => s • νx a + t • νy a,
    fun a ha => obedienceRegion_convex u a (hνx a ha) (hνy a ha) hs ht hst, fun ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx ω, hy ω, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma ident_nonempty {u : Ω → A → ℝ} {α : A → ℝ} (hdom : NoSupportedActionDominated u α) :
    (identifiedSet u α).Nonempty := by
  choose! ν hν using fun a (ha : a ∈ supp α) => hdom a ha
  exact ⟨_, ν, hν, fun ω => rfl⟩

lemma RO_isCompact (u : Ω → A → ℝ) (α : A → ℝ) : IsCompact (robustlyObedientPolicies u α) := by
  have hcl : IsClosed (robustlyObedientPolicies u α) := by
    have h1 : IsClosed {π : Ω → A → ℝ | ∀ ω a, 0 ≤ π ω a} := by
      have : {π : Ω → A → ℝ | ∀ ω a, 0 ≤ π ω a} = ⋂ ω, ⋂ a, {π | 0 ≤ π ω a} := by ext; simp
      rw [this]
      exact isClosed_iInter fun ω => isClosed_iInter fun a => isClosed_le continuous_const
        ((continuous_apply a).comp (continuous_apply ω))
    have h2 : IsClosed {π : Ω → A → ℝ | ∀ ω, ∑ a, π ω a = 1} := by
      have : {π : Ω → A → ℝ | ∀ ω, ∑ a, π ω a = 1} = ⋂ ω, {π | ∑ a, π ω a = 1} := by ext; simp
      rw [this]
      exact isClosed_iInter fun ω => isClosed_eq
        (continuous_finset_sum _ fun a _ => (continuous_apply a).comp (continuous_apply ω))
        continuous_const
    have h3 : IsClosed {π : Ω → A → ℝ | ∀ ω a, a ∉ supp α → π ω a = 0} := by
      have : {π : Ω → A → ℝ | ∀ ω a, a ∉ supp α → π ω a = 0} =
          ⋂ ω, ⋂ a, ⋂ (_ : a ∉ supp α), {π | π ω a = 0} := by ext; simp
      rw [this]
      exact isClosed_iInter fun ω => isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_eq ((continuous_apply a).comp (continuous_apply ω)) continuous_const
    have h4 : IsClosed {π : Ω → A → ℝ | ∀ μ ∈ identifiedSet u α, ∀ a ∈ supp α, ∀ a' : A,
        0 ≤ ∑ ω, π ω a * μ ω * (u ω a - u ω a')} := by
      have : {π : Ω → A → ℝ | ∀ μ ∈ identifiedSet u α, ∀ a ∈ supp α, ∀ a' : A,
          0 ≤ ∑ ω, π ω a * μ ω * (u ω a - u ω a')} =
          ⋂ μ, ⋂ (_ : μ ∈ identifiedSet u α), ⋂ a, ⋂ (_ : a ∈ supp α), ⋂ a',
            {π | 0 ≤ ∑ ω, π ω a * μ ω * (u ω a - u ω a')} := by ext; simp
      rw [this]
      exact isClosed_iInter fun μ => isClosed_iInter fun _ => isClosed_iInter fun a =>
        isClosed_iInter fun _ => isClosed_iInter fun a' => isClosed_le continuous_const
          (continuous_finset_sum _ fun ω _ => by fun_prop)
    have h5 := (h1.inter (h2.inter h3)).inter h4
    exact h5
  refine (isCompact_univ_pi fun ω => isCompact_univ_pi fun a => isCompact_Icc (a := (0 : ℝ))
    (b := 1)).of_isClosed_subset hcl ?_
  intro π hπ
  rw [Set.mem_univ_pi]
  intro ω
  rw [Set.mem_univ_pi]
  intro a
  exact ⟨hπ.1.1 ω a, pi_le_one hπ.1 ω a⟩

lemma RO_convex (u : Ω → A → ℝ) (α : A → ℝ) : Convex ℝ (robustlyObedientPolicies u α) := by
  intro π1 h1 π2 h2 s t hs ht hst
  have hsup : s • π1 + t • π2 ∈ supportedPolicies α :=
    ⟨fun ω a => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hs (h1.1.1 ω a)) (mul_nonneg ht (h2.1.1 ω a)),
     fun ω => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1.1.2.1 ω, h2.1.2.1 ω]
      linarith,
     fun ω a ha => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h1.1.2.2 ω a ha, h2.1.2.2 ω a ha]; ring⟩
  refine ⟨hsup, fun μ hμ a ha a' => ?_⟩
  have e : obedienceMargin u (s • π1 + t • π2) a a' μ =
      s * obedienceMargin u π1 a a' μ + t * obedienceMargin u π2 a a' μ := by
    unfold obedienceMargin
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  show 0 ≤ obedienceMargin u (s • π1 + t • π2) a a' μ
  rw [e]
  exact add_nonneg (mul_nonneg hs (h1.2 μ hμ a ha a')) (mul_nonneg ht (h2.2 μ hμ a ha a'))

lemma sp_cont_pi (v : Ω → A → ℝ) (α : A → ℝ) (μ : Ω → ℝ) :
    Continuous fun π : Ω → A → ℝ => senderPayoff v α π μ := by
  unfold senderPayoff
  exact continuous_finset_sum _ fun ω _ => continuous_finset_sum _ fun a _ =>
    by fun_prop

lemma sp_cont_mu (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) :
    Continuous fun μ : Ω → ℝ => senderPayoff v α π μ := by
  unfold senderPayoff
  exact continuous_finset_sum _ fun ω _ => continuous_finset_sum _ fun a _ =>
    by fun_prop

lemma sp_comb (v : Ω → A → ℝ) (α : A → ℝ) (μ : Ω → ℝ) (π π' : Ω → A → ℝ) (s t : ℝ) :
    senderPayoff v α (s • π + t • π') μ =
      s * senderPayoff v α π μ + t * senderPayoff v α π' μ := by
  unfold senderPayoff
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma sp_comb_mu (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) (μ μ' : Ω → ℝ) (s t : ℝ) :
    senderPayoff v α π (s • μ + t • μ') =
      s * senderPayoff v α π μ + t * senderPayoff v α π μ' := by
  unfold senderPayoff
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma sp_dot (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) (μ : Ω → ℝ) :
    senderPayoff v α π μ = ∑ ω, μ ω * ∑ a ∈ supp α, π ω a * v ω a := by
  unfold senderPayoff
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma sp_sum_mu {ι : Type*} [Fintype ι] (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ)
    (lam : ι → ℝ) (y : ι → Ω → ℝ) :
    senderPayoff v α π (∑ i, lam i • y i) = ∑ i, lam i * senderPayoff v α π (y i) := by
  have key : ∀ c : Ω → ℝ, ∑ ω, (∑ i, lam i • y i) ω * c ω = ∑ i, lam i * ∑ ω, y i ω * c ω := by
    intro c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ω _ => by ring
  have := key (fun ω => ∑ a ∈ supp α, π ω a * v ω a)
  simp only [sp_dot]
  exact this

noncomputable def spL (v : Ω → A → ℝ) (α : A → ℝ) (μ : Ω → ℝ) : (Ω → A → ℝ) →ₗ[ℝ] ℝ where
  toFun π := senderPayoff v α π μ
  map_add' π π' := by
    have := sp_comb v α μ π π' 1 1
    simpa using this
  map_smul' c π := by
    have := sp_comb v α μ π 0 c 0
    simpa using this

lemma sp_sum_pi {ι : Type*} [Fintype ι] (v : Ω → A → ℝ) (α : A → ℝ) (μ : Ω → ℝ)
    (lam : ι → ℝ) (π : ι → Ω → A → ℝ) :
    senderPayoff v α (∑ i, lam i • π i) μ = ∑ i, lam i * senderPayoff v α (π i) μ := by
  have h := map_sum (spL v α μ) (fun i => lam i • π i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma exists_extreme_min {S : Set (Ω → ℝ)} (hS : IsCompact S) (hn : S.Nonempty)
    (φ : (Ω → ℝ) → ℝ) (hc : Continuous φ)
    (haff : ∀ x y (a b : ℝ), a + b = 1 → φ (a • x + b • y) = a * φ x + b * φ y) :
    ∃ x ∈ S.extremePoints ℝ, ∀ y ∈ S, φ x ≤ φ y := by
  obtain ⟨x0, hx0S, hmin⟩ := hS.exists_isMinOn hn hc.continuousOn
  have hm : ∀ y ∈ S, φ x0 ≤ φ y := fun y hy => hmin hy
  set F : Set (Ω → ℝ) := S ∩ {x | φ x = φ x0} with hF
  have hFc : IsCompact F := hS.inter_right (isClosed_eq hc continuous_const)
  have hext : IsExtreme ℝ S F := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro x1 hx1 x2 hx2 x hx hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have e := haff x1 x2 a b hab
    have hxF : φ (a • x1 + b • x2) = φ x0 := hx.2
    have h1 := hm x1 hx1
    have h2 := hm x2 hx2
    have p1 : 0 ≤ a * (φ x1 - φ x0) := mul_nonneg ha.le (by linarith)
    have p2 : 0 ≤ b * (φ x2 - φ x0) := mul_nonneg hb.le (by linarith)
    have hsum : a * (φ x1 - φ x0) + b * (φ x2 - φ x0) = 0 := by
      have : a * φ x0 + b * φ x0 = φ x0 := by rw [← add_mul, hab, one_mul]
      nlinarith
    have q1 : a * (φ x1 - φ x0) = 0 := by linarith
    have q2 : b * (φ x2 - φ x0) = 0 := by linarith
    have r1 : φ x1 - φ x0 = 0 := (mul_eq_zero.mp q1).resolve_left ha.ne'
    have r2 : φ x2 - φ x0 = 0 := (mul_eq_zero.mp q2).resolve_left hb.ne'
    exact ⟨hx1, show φ x1 = φ x0 by linarith⟩
  obtain ⟨x, hx⟩ := hFc.extremePoints_nonempty ⟨x0, hx0S, rfl⟩
  exact ⟨x, hext.extremePoints_subset_extremePoints hx, fun y hy => by
    have := hx.1.2
    have := hm y hy
    simp only [Set.mem_setOf_eq] at *
    linarith⟩

end

end RobustObedientPersuasion.Saddle.Dev
end

section
namespace RobustObedientPersuasion.Saddle
open RobustObedientPersuasion.Saddle.Supplement RobustObedientPersuasion.Saddle.Supplement.Dev
  RobustObedientPersuasion.Saddle.Dev

theorem chk_theorem_3_1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u v : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α)
    (hRO : (robustlyObedientPolicies u α).Nonempty) :
    -- for every policy, the inner minimum over priors is attained
    (∀ π ∈ robustlyObedientPolicies u α,
      ∃ m, IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) m) ∧
    -- for every prior, the inner maximum over policies is attained
    (∀ μ ∈ identifiedSet u α,
      ∃ M, IsGreatest ((fun π => senderPayoff v α π μ) '' robustlyObedientPolicies u α) M) ∧
    -- max_π min_μ V = min_μ max_π V, both outer extrema attained
    (∃ w : ℝ,
      IsGreatest {x | ∃ π ∈ robustlyObedientPolicies u α,
        IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) x} w ∧
      IsLeast {x | ∃ μ ∈ identifiedSet u α,
        IsGreatest ((fun π => senderPayoff v α π μ) '' robustlyObedientPolicies u α) x} w) ∧
    -- a pure-strategy saddle point
    (∃ πs ∈ robustlyObedientPolicies u α, ∃ μs ∈ identifiedSet u α,
      ∀ π ∈ robustlyObedientPolicies u α, ∀ μ ∈ identifiedSet u α,
        senderPayoff v α π μs ≤ senderPayoff v α πs μs ∧
          senderPayoff v α πs μs ≤ senderPayoff v α πs μ) ∧
    -- for every fixed policy, the inner minimum is attained at an extreme point of P(α)
    (∀ π ∈ robustlyObedientPolicies u α,
      ∃ μhat ∈ Set.extremePoints ℝ (identifiedSet u α),
        ∀ μ ∈ identifiedSet u α, senderPayoff v α π μhat ≤ senderPayoff v α π μ) ∧
    -- in particular, every maxmin-optimal policy admits a worst-case prior in ext(P(α))
    (∀ πs ∈ robustlyObedientPolicies u α,
      (∃ m, IsLeast ((fun μ => senderPayoff v α πs μ) '' identifiedSet u α) m ∧
        IsGreatest {x | ∃ π ∈ robustlyObedientPolicies u α,
          IsLeast ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) x} m) →
      ∃ μhat ∈ Set.extremePoints ℝ (identifiedSet u α),
        ∀ μ ∈ identifiedSet u α, senderPayoff v α πs μhat ≤ senderPayoff v α πs μ) := by
  set K := robustlyObedientPolicies u α with hK
  set P := identifiedSet u α with hP
  have hKc : IsCompact K := RO_isCompact u α
  have hKv : Convex ℝ K := RO_convex u α
  have hPc : IsCompact P := ident_compact u α
  have hPv : Convex ℝ P := ident_convex u α
  have hPn : P.Nonempty := ident_nonempty hdom
  obtain ⟨π0, hπ0⟩ := hRO
  have hinf : ∀ π, ∃ m, IsLeast ((fun μ => senderPayoff v α π μ) '' P) m := fun π =>
    (hPc.image (sp_cont_mu v α π)).exists_isLeast (hPn.image _)
  have hsup : ∀ μ, ∃ M, IsGreatest ((fun π => senderPayoff v α π μ) '' K) M := fun μ =>
    (hKc.image (sp_cont_pi v α μ)).exists_isGreatest (Set.Nonempty.image _ (⟨π0, hπ0⟩ : K.Nonempty))
  have hsaddle : ∃ πs ∈ K, ∃ μs ∈ P, ∀ π ∈ K, ∀ μ ∈ P,
      senderPayoff v α π μs ≤ senderPayoff v α πs μs ∧
        senderPayoff v α πs μs ≤ senderPayoff v α πs μ := by
    set E2 : Set ℝ := {x | ∃ μ ∈ P, IsGreatest ((fun π => senderPayoff v α π μ) '' K) x}
      with hE2
    set E1 : Set ℝ := {x | ∃ π ∈ K, IsLeast ((fun μ => senderPayoff v α π μ) '' P) x} with hE1
    obtain ⟨μ0, hμ0⟩ := hPn
    obtain ⟨M0, hM0⟩ := hsup μ0
    obtain ⟨m0, hm0⟩ := hinf π0
    have hE2ne : E2.Nonempty := ⟨M0, μ0, hμ0, hM0⟩
    have hE1ne : E1.Nonempty := ⟨m0, π0, hπ0, hm0⟩
    have hE2bdd : BddBelow E2 := ⟨m0, by
      rintro x ⟨μ, hμ, hx⟩
      exact (hm0.2 ⟨μ, hμ, rfl⟩).trans (hx.2 ⟨π0, hπ0, rfl⟩)⟩
    have hE1bdd : BddAbove E1 := ⟨M0, by
      rintro x ⟨π, hπ, hx⟩
      exact (hx.2 ⟨μ0, hμ0, rfl⟩).trans (hM0.2 ⟨π, hπ, rfl⟩)⟩
    have hweak : ∀ x, x ∈ E1 → ∀ y, y ∈ E2 → x ≤ y := by
      rintro x ⟨π, hπ, hx⟩ y ⟨μ, hμ, hy⟩
      exact (hx.2 ⟨μ, hμ, rfl⟩).trans (hy.2 ⟨π, hπ, rfl⟩)
    have hc_le : sSup E1 ≤ sInf E2 :=
      csSup_le hE1ne fun x hx => le_csInf hE2ne fun y hy => hweak x hx y hy
    obtain ⟨πs, hπs, hπsge⟩ := minimax_exists K hKc hKv ⟨π0, hπ0⟩ P hPv
      (fun π μ => senderPayoff v α π μ) (fun μ => sp_cont_pi v α μ)
      (fun μ x1 x2 a b _ => sp_comb v α μ x1 x2 a b)
      (fun ι _ lam y _ x => sp_sum_mu v α x lam y) (sInf E2) (by
        intro μ hμ
        obtain ⟨M, hM⟩ := hsup μ
        obtain ⟨π, hπ, hπM⟩ := hM.1
        exact ⟨π, hπ, (csInf_le hE2bdd ⟨μ, hμ, hM⟩).trans_eq hπM.symm⟩)
    obtain ⟨μs, hμs, hμsle⟩ := minimax_exists (X := Ω → ℝ) P hPc hPv ⟨μ0, hμ0⟩ K hKv
      (fun μ π => - senderPayoff v α π μ) (fun π => (sp_cont_mu v α π).neg)
      (fun π μ1 μ2 a b _ => by
        show -senderPayoff v α π (a • μ1 + b • μ2) = _
        rw [sp_comb_mu]; ring)
      (fun ι _ lam π _ μ => by
        show -senderPayoff v α (∑ i, lam i • π i) μ = ∑ i, lam i * -senderPayoff v α (π i) μ
        rw [sp_sum_pi, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (-(sSup E1)) (by
        intro π hπ
        obtain ⟨m, hm⟩ := hinf π
        obtain ⟨μ, hμ, hμm⟩ := hm.1
        refine ⟨μ, hμ, ?_⟩
        have h1 : m ≤ sSup E1 := le_csSup hE1bdd ⟨π, hπ, hm⟩
        show -(sSup E1) ≤ -senderPayoff v α π μ
        have h2 : senderPayoff v α π μ = m := hμm
        linarith)
    have hle1 : ∀ π ∈ K, senderPayoff v α π μs ≤ sSup E1 := by
      intro π hπ
      have h := hμsle π hπ
      have h' : -(sSup E1) ≤ -senderPayoff v α π μs := h
      linarith
    have hge1 : ∀ μ ∈ P, sInf E2 ≤ senderPayoff v α πs μ := hπsge
    have hmid := hge1 μs hμs
    have hmid2 := hle1 πs hπs
    refine ⟨πs, hπs, μs, hμs, fun π hπ μ hμ => ⟨?_, ?_⟩⟩
    · have := hle1 π hπ
      linarith
    · have := hge1 μ hμ
      linarith
  obtain ⟨πs, hπs, μs, hμs, hsad⟩ := hsaddle
  have h5 : ∀ π ∈ K, ∃ μhat ∈ Set.extremePoints ℝ P, ∀ μ ∈ P,
      senderPayoff v α π μhat ≤ senderPayoff v α π μ := fun π _ =>
    exists_extreme_min hPc hPn (fun μ => senderPayoff v α π μ) (sp_cont_mu v α π)
      (fun x y a b _ => sp_comb_mu v α π x y a b)
  refine ⟨fun π _ => hinf π, fun μ _ => hsup μ, ?_, ⟨πs, hπs, μs, hμs, hsad⟩, h5,
    fun πs' hπs' _ => h5 πs' hπs'⟩
  refine ⟨senderPayoff v α πs μs, ⟨⟨πs, hπs, ⟨⟨μs, hμs, rfl⟩, ?_⟩⟩, ?_⟩, ⟨μs, hμs, ⟨⟨πs, hπs, rfl⟩, ?_⟩⟩, ?_⟩
  · rintro _ ⟨μ, hμ, rfl⟩
    exact (hsad πs hπs μ hμ).2
  · rintro x ⟨π, hπ, hx⟩
    exact (hx.2 ⟨μs, hμs, rfl⟩).trans (hsad π hπ μs hμs).1
  · rintro _ ⟨π, hπ, rfl⟩
    exact (hsad π hπ μs hμs).1
  · rintro y ⟨μ, hμ, hy⟩
    exact (hsad πs hπs μ hμ).2.trans (hy.2 ⟨πs, hπs, rfl⟩)

end RobustObedientPersuasion.Saddle
end

theorem solution : type_of% @RobustObedientPersuasion.Saddle.chk_theorem_3_1 := @RobustObedientPersuasion.Saddle.chk_theorem_3_1
