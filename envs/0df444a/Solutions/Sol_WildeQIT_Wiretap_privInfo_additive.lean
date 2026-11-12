-- Prove2me | solution 1 for WildeQIT.Wiretap.privInfo_additive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T14:51:30.631068+00:00
-- url     : https://prove2.me/submissions/4e4c0c34-c1f0-4557-8d1b-b75b98bd3b08

import Mathlib
import Definitions.Def_WildeQIT_Wiretap_privInfo
import Definitions.Def_WildeQIT_Wiretap_prodWiretap

set_option autoImplicit false

namespace WildeQIT.PrivAdd

open WildeQIT WildeQIT.Wiretap

noncomputable def ent1 (x : ℝ) : ℝ := x * Real.logb 2 x

noncomputable def nl {ι : Type} [Fintype ι] (f : ι → ℝ) : ℝ := ∑ i, ent1 (f i)

lemma ent1_mul (a b : ℝ) : ent1 (a * b) = ent1 a * b + a * ent1 b := by
  unfold ent1
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  rw [Real.logb_mul ha hb]; ring

lemma ent1_smul (c a : ℝ) : ent1 (c * a) = c * ent1 a + Real.logb 2 c * c * a := by
  rw [ent1_mul]; unfold ent1; ring

lemma nl_prod {A B : Type} [Fintype A] [Fintype B] (f : A → ℝ) (g : B → ℝ) :
    nl (fun ab : A × B => f ab.1 * g ab.2) = nl f * ∑ b, g b + (∑ a, f a) * nl g := by
  unfold nl
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact ent1_mul _ _

lemma nl_equiv {A B : Type} [Fintype A] [Fintype B] (e : B ≃ A) (f : A → ℝ) :
    nl (fun b => f (e b)) = nl f := by
  unfold nl; exact Equiv.sum_comp e (fun a => ent1 (f a))

lemma nl_tensor {A1 A2 B : Type} [Fintype A1] [Fintype A2] [Fintype B] (f : A1 → ℝ) (g : A2 → ℝ)
    (e : B ≃ A1 × A2) (h : B → ℝ) (hh : ∀ b, h b = f (e b).1 * g (e b).2)
    (hf : ∑ a, f a = 1) (hg : ∑ a, g a = 1) : nl h = nl f + nl g := by
  calc nl h = nl (fun b => (fun w : A1 × A2 => f w.1 * g w.2) (e b)) := by
        congr 1; exact funext hh
    _ = nl (fun w : A1 × A2 => f w.1 * g w.2) := nl_equiv e (fun w : A1 × A2 => f w.1 * g w.2)
    _ = nl f + nl g := by rw [nl_prod, hf, hg]; ring

lemma rev3 {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (F : A → B → C → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, F a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := Finset.sum_comm

lemma mutualInfo_eq {α β : Type} [Fintype α] [Fintype β] (q : FinDist (α × β)) :
    mutualInfo q = nl q.prob - nl q.fst.prob - nl q.snd.prob := by
  have key : ∀ x y, q.prob (x, y) * Real.logb 2 (q.prob (x, y) / q.snd.prob y)
      = ent1 (q.prob (x, y)) - q.prob (x, y) * Real.logb 2 (q.snd.prob y) := by
    intro x y
    unfold ent1
    rcases eq_or_ne (q.prob (x, y)) 0 with h | h
    · simp [h]
    · have hle : q.prob (x, y) ≤ q.snd.prob y := by
        rw [FinDist.snd_prob]
        exact Finset.single_le_sum (f := fun x' => q.prob (x', y)) (fun i _ => q.nonneg (i, y))
          (Finset.mem_univ x)
      have hpos : 0 < q.prob (x, y) := lt_of_le_of_ne (q.nonneg _) (Ne.symm h)
      rw [Real.logb_div h (ne_of_gt (lt_of_lt_of_le hpos hle))]
      ring
  have hc : condEntropy q = -(nl q.prob - nl q.snd.prob) := by
    unfold condEntropy
    simp only [key, Finset.sum_sub_distrib]
    have h2 : ∑ x, ∑ y, q.prob (x, y) * Real.logb 2 (q.snd.prob y) = nl q.snd.prob := by
      rw [Finset.sum_comm]
      unfold nl ent1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [FinDist.snd_prob, Finset.sum_mul]
    rw [h2]
    unfold nl
    rw [Fintype.sum_prod_type]
  unfold mutualInfo entropy
  rw [hc]
  unfold nl ent1
  ring

/-- `I(U;Y) - I(U;Z)` as a functional of an (unnormalised) joint weight `J` on `U × Y × Z`. -/
noncomputable def Qf {υ β γ : Type} [Fintype υ] [Fintype β] [Fintype γ] (J : υ × β × γ → ℝ) : ℝ :=
  nl (fun uy : υ × β => ∑ z, J (uy.1, uy.2, z)) - nl (fun y : β => ∑ u, ∑ z, J (u, y, z))
  - nl (fun uz : υ × γ => ∑ y, J (uz.1, y, uz.2)) + nl (fun z : γ => ∑ u, ∑ y, J (u, y, z))

lemma msum {υ β γ : Type} [Fintype υ] [Fintype β] [Fintype γ] (J : υ × β × γ → ℝ) :
    (∑ uy : υ × β, ∑ z, J (uy.1, uy.2, z)) = ∑ t, J t ∧
    (∑ y : β, ∑ u, ∑ z, J (u, y, z)) = ∑ t, J t ∧
    (∑ uz : υ × γ, ∑ y, J (uz.1, y, uz.2)) = ∑ t, J t ∧
    (∑ z : γ, ∑ u, ∑ y, J (u, y, z)) = ∑ t, J t ∧
    (∑ u : υ, ∑ y, ∑ z, J (u, y, z)) = ∑ t, J t := by
  have hS : ∑ t, J t = ∑ u, ∑ y, ∑ z, J (u, y, z) := by
    simp only [Fintype.sum_prod_type]
  refine ⟨?_, ?_, ?_, ?_, hS.symm⟩
  · rw [hS, Fintype.sum_prod_type]
  · rw [hS]; exact Finset.sum_comm
  · rw [hS, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
  · rw [hS, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

lemma Qf_smul {υ β γ : Type} [Fintype υ] [Fintype β] [Fintype γ] (c : ℝ) (J : υ × β × γ → ℝ) :
    Qf (fun t => c * J t) = c * Qf J := by
  obtain ⟨s1, s2, s3, s4, -⟩ := msum J
  unfold Qf nl
  simp only [← Finset.mul_sum, ent1_smul, Finset.sum_add_distrib]
  linear_combination (Real.logb 2 c * c) * (s1 - s2 - s3 + s4)

lemma Q_eq_Qf {υ α β γ : Type} [Fintype υ] [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (υ × α)) (N : WiretapChannel α β γ) :
    mutualInfo (wiretapJoint p N).margXY - mutualInfo (wiretapJoint p N).margXZ
      = Qf (wiretapJoint p N).prob := by
  rw [mutualInfo_eq, mutualInfo_eq]
  have h1 : (wiretapJoint p N).margXY.fst.prob = (wiretapJoint p N).margXZ.fst.prob := by
    funext u
    simp only [FinDist.fst_prob, FinDist.margXY_prob, FinDist.margXZ_prob]
    exact Finset.sum_comm
  have h2 : Qf (wiretapJoint p N).prob = nl (wiretapJoint p N).margXY.prob
      - nl (wiretapJoint p N).margXY.snd.prob - nl (wiretapJoint p N).margXZ.prob
      + nl (wiretapJoint p N).margXZ.snd.prob := rfl
  rw [h1, h2]; ring

lemma pt {q a : ℝ} (hq : 0 ≤ q) (hqa : q ≤ a) :
    q * Real.logb 2 a - ent1 q ≤ a / Real.log 2 := by
  unfold ent1
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    simp only [zero_mul, sub_zero]
    exact div_nonneg hqa hl.le
  · have ha : 0 < a := lt_of_lt_of_le h hqa
    have key : q * Real.log (a / q) ≤ a - q := by
      have := Real.log_le_sub_one_of_pos (div_pos ha h)
      calc q * Real.log (a / q) ≤ q * (a / q - 1) := mul_le_mul_of_nonneg_left this hq
        _ = a - q := by field_simp
    rw [Real.log_div ha.ne' h.ne'] at key
    simp only [Real.logb]
    rw [le_div_iff₀ hl]
    have e : (q * (Real.log a / Real.log 2) - q * (Real.log q / Real.log 2)) * Real.log 2
        = q * (Real.log a - Real.log q) := by
      rw [sub_mul, mul_assoc, mul_assoc, div_mul_cancel₀ _ hl.ne', div_mul_cancel₀ _ hl.ne']
      ring
    rw [e]; linarith

lemma Qf_bound {υ β γ : Type} [Fintype υ] [Fintype β] [Fintype γ] (J : υ × β × γ → ℝ)
    (hJ : ∀ t, 0 ≤ J t) (h1 : ∑ t, J t = 1) :
    Qf J ≤ ((Fintype.card β : ℝ) + Fintype.card γ) / Real.log 2 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := msum J
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : nl (fun uy : υ × β => ∑ z, J (uy.1, uy.2, z))
      ≤ nl (fun u : υ => ∑ y, ∑ z, J (u, y, z)) := by
    unfold nl
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    calc ∑ y, ent1 (∑ z, J (u, y, z))
        ≤ ∑ y, (∑ z, J (u, y, z)) * Real.logb 2 (∑ y', ∑ z', J (u, y', z')) := by
          refine Finset.sum_le_sum fun y _ => ?_
          unfold ent1
          have h0 : 0 ≤ ∑ z, J (u, y, z) := Finset.sum_nonneg fun z _ => hJ _
          rcases eq_or_lt_of_le h0 with h | h
          · rw [← h]; simp
          · apply mul_le_mul_of_nonneg_left _ h0
            apply Real.logb_le_logb_of_le one_lt_two h
            exact Finset.single_le_sum (f := fun y => ∑ z, J (u, y, z))
              (fun y _ => Finset.sum_nonneg fun z _ => hJ _) (Finset.mem_univ y)
      _ = ent1 (∑ y', ∑ z', J (u, y', z')) := by unfold ent1; rw [Finset.sum_mul]
  have hB : nl (fun u : υ => ∑ y, ∑ z, J (u, y, z)) - nl (fun uz : υ × γ => ∑ y, J (uz.1, y, uz.2))
      ≤ Fintype.card γ / Real.log 2 := by
    have hUz : ∀ u, ∑ y, ∑ z, J (u, y, z) = ∑ z, ∑ y, J (u, y, z) := fun u => Finset.sum_comm
    have e1 : nl (fun u : υ => ∑ y, ∑ z, J (u, y, z))
        = ∑ u, ∑ z, (∑ y, J (u, y, z)) * Real.logb 2 (∑ y', ∑ z', J (u, y', z')) := by
      unfold nl ent1
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, ← hUz]
    have e2 : nl (fun uz : υ × γ => ∑ y, J (uz.1, y, uz.2))
        = ∑ u, ∑ z, ent1 (∑ y, J (u, y, z)) := by
      unfold nl; rw [Fintype.sum_prod_type]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    calc ∑ u, (∑ z, (∑ y, J (u, y, z)) * Real.logb 2 (∑ y', ∑ z', J (u, y', z'))
          - ∑ z, ent1 (∑ y, J (u, y, z)))
        ≤ ∑ u, ∑ z : γ, (∑ y', ∑ z', J (u, y', z')) / Real.log 2 := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun z _ => ?_
          apply pt (Finset.sum_nonneg fun y _ => hJ _)
          rw [hUz]
          exact Finset.single_le_sum (f := fun z => ∑ y, J (u, y, z))
            (fun z _ => Finset.sum_nonneg fun y _ => hJ _) (Finset.mem_univ z)
      _ = Fintype.card γ / Real.log 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum, ← Finset.sum_div, s5, h1]; ring
  have hC : -nl (fun y : β => ∑ u, ∑ z, J (u, y, z)) ≤ Fintype.card β / Real.log 2 := by
    unfold nl
    rw [← Finset.sum_neg_distrib]
    calc ∑ y, -ent1 (∑ u, ∑ z, J (u, y, z)) ≤ ∑ _y : β, 1 / Real.log 2 := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hle : ∑ u, ∑ z, J (u, y, z) ≤ 1 := by
            rw [← h1, ← s2]
            exact Finset.single_le_sum (f := fun y => ∑ u, ∑ z, J (u, y, z))
              (fun y _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun z _ => hJ _)
              (Finset.mem_univ y)
          have := pt (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun z _ => hJ (u, y, z)) hle
          rw [Real.logb_one, mul_zero, zero_sub] at this
          exact this
      _ = Fintype.card β / Real.log 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hD : nl (fun z : γ => ∑ u, ∑ y, J (u, y, z)) ≤ 0 := by
    unfold nl
    refine Finset.sum_nonpos fun z _ => ?_
    unfold ent1
    have h0 : 0 ≤ ∑ u, ∑ y, J (u, y, z) :=
      Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun y _ => hJ _
    have hle : ∑ u, ∑ y, J (u, y, z) ≤ 1 := by
      rw [← h1, ← s4]
      exact Finset.single_le_sum (f := fun z => ∑ u, ∑ y, J (u, y, z))
        (fun z _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun y _ => hJ _)
        (Finset.mem_univ z)
    exact mul_nonpos_iff.mpr (Or.inl ⟨h0, Real.logb_nonpos one_lt_two h0 hle⟩)
  unfold Qf
  rw [add_div]
  linarith

lemma bdd {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (N : WiretapChannel α β γ) :
    BddAbove {r : ℝ | ∃ (n : ℕ) (p : FinDist (Fin n × α)),
      r = mutualInfo (wiretapJoint p N).margXY - mutualInfo (wiretapJoint p N).margXZ} := by
  refine ⟨((Fintype.card β : ℝ) + Fintype.card γ) / Real.log 2, ?_⟩
  rintro r ⟨n, p, rfl⟩
  rw [Q_eq_Qf]
  exact Qf_bound _ (wiretapJoint p N).nonneg (wiretapJoint p N).sum_eq_one

lemma setne {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α]
    (N : WiretapChannel α β γ) :
    Set.Nonempty {r : ℝ | ∃ (n : ℕ) (p : FinDist (Fin n × α)),
      r = mutualInfo (wiretapJoint p N).margXY - mutualInfo (wiretapJoint p N).margXZ} := by
  classical
  obtain ⟨a⟩ := ‹Nonempty α›
  let p : FinDist (Fin 1 × α) :=
    { prob := fun t => if t = (0, a) then 1 else 0
      nonneg := fun t => by split_ifs <;> norm_num
      sum_eq_one := by simp }
  exact ⟨_, 1, p, rfl⟩

lemma Qf_le {n : ℕ} {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (N : WiretapChannel α β γ) (G : Fin n × α → ℝ) (hG : ∀ t, 0 ≤ G t) :
    Qf (fun t : Fin n × β × γ => ∑ x, G (t.1, x) * (N x).prob t.2)
      ≤ (∑ t, G t) * privInfo N := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun t _ => hG t : (0:ℝ) ≤ ∑ t, G t) with hc | hc
  · have hG0 : ∀ t, G t = 0 := fun t =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hG t)).1 hc.symm t (Finset.mem_univ t)
    rw [← hc, zero_mul]
    simp [Qf, nl, ent1, hG0]
  · let p : FinDist (Fin n × α) :=
      { prob := fun t => G t / (∑ s, G s)
        nonneg := fun t => div_nonneg (hG t) hc.le
        sum_eq_one := by rw [← Finset.sum_div]; exact div_self hc.ne' }
    have hJ : (wiretapJoint p N).prob
        = fun t => (∑ s, G s)⁻¹ * ∑ x, G (t.1, x) * (N x).prob t.2 := by
      funext t
      show ∑ x, G (t.1, x) / (∑ s, G s) * (N x).prob t.2 = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have hQ := Q_eq_Qf p N
    rw [hJ, Qf_smul] at hQ
    have hmem : (∑ s, G s)⁻¹ * Qf (fun t : Fin n × β × γ => ∑ x, G (t.1, x) * (N x).prob t.2)
        ≤ privInfo N := le_csSup (bdd N) ⟨n, p, hQ.symm⟩
    have := mul_le_mul_of_nonneg_left hmem hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this

set_option maxHeartbeats 1000000 in
lemma split_id {υ β₁ γ₁ β₂ γ₂ : Type} [Fintype υ] [Fintype β₁] [Fintype γ₁] [Fintype β₂]
    [Fintype γ₂] (M : υ → β₁ → γ₁ → β₂ → γ₂ → ℝ) :
    Qf (fun t : υ × (β₁ × β₂) × (γ₁ × γ₂) => M t.1 t.2.1.1 t.2.2.1 t.2.1.2 t.2.2.2)
      = ∑ y1, Qf (fun t : υ × β₂ × γ₂ => ∑ z1, M t.1 y1 z1 t.2.1 t.2.2)
        + ∑ z2, Qf (fun t : υ × β₁ × γ₁ => ∑ y2, M t.1 t.2.1 t.2.2 y2 z2) := by
  unfold Qf nl
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ u, ∑ y1, ∑ y2, ent1 (∑ z1, ∑ z2, M u y1 z1 y2 z2)
      = ∑ y1, ∑ u, ∑ y2, ent1 (∑ z2, ∑ z1, M u y1 z1 y2 z2) :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun y2 _ => congrArg ent1 Finset.sum_comm)
  have e2 : ∑ y1, ∑ y2, ent1 (∑ u, ∑ z1, ∑ z2, M u y1 z1 y2 z2)
      = ∑ y1, ∑ y2, ent1 (∑ u, ∑ z2, ∑ z1, M u y1 z1 y2 z2) :=
    Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
      congrArg ent1 (Finset.sum_congr rfl fun u _ => Finset.sum_comm)
  have e3 : ∑ y1, ∑ u, ∑ z2, ent1 (∑ y2, ∑ z1, M u y1 z1 y2 z2)
      = ∑ z2, ∑ u, ∑ y1, ent1 (∑ z1, ∑ y2, M u y1 z1 y2 z2) :=
    (rev3 _).trans (Finset.sum_congr rfl fun z2 _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun y1 _ => congrArg ent1 Finset.sum_comm)
  have e4 : ∑ y1, ∑ z2, ent1 (∑ u, ∑ y2, ∑ z1, M u y1 z1 y2 z2)
      = ∑ z2, ∑ y1, ent1 (∑ u, ∑ z1, ∑ y2, M u y1 z1 y2 z2) :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun z2 _ => Finset.sum_congr rfl fun y1 _ =>
      congrArg ent1 (Finset.sum_congr rfl fun u _ => Finset.sum_comm))
  have e5 : ∑ z2, ∑ u, ∑ z1, ent1 (∑ y1, ∑ y2, M u y1 z1 y2 z2)
      = ∑ u, ∑ z1, ∑ z2, ent1 (∑ y1, ∑ y2, M u y1 z1 y2 z2) :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun u _ => Finset.sum_comm)
  have e6 : ∑ z2, ∑ z1, ent1 (∑ u, ∑ y1, ∑ y2, M u y1 z1 y2 z2)
      = ∑ z1, ∑ z2, ent1 (∑ u, ∑ y1, ∑ y2, M u y1 z1 y2 z2) := Finset.sum_comm
  linarith [e1, e2, e3, e4, e5, e6]

set_option maxHeartbeats 1000000 in
theorem le_dir {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type} [Fintype α₁] [Fintype α₂] [Fintype β₁]
    [Fintype β₂] [Fintype γ₁] [Fintype γ₂] [Nonempty α₁] [Nonempty α₂]
    (N₁ : WiretapChannel α₁ β₁ γ₁) (N₂ : WiretapChannel α₂ β₂ γ₂) :
    privInfo (prodWiretap N₁ N₂) ≤ privInfo N₁ + privInfo N₂ := by
  apply csSup_le (setne _)
  rintro r ⟨n, p, rfl⟩
  rw [Q_eq_Qf]
  have hsplit := split_id (fun (u : Fin n) (y1 : β₁) (z1 : γ₁) (y2 : β₂) (z2 : γ₂) =>
    ∑ x : α₁ × α₂, p.prob (u, x) * ((N₁ x.1).prob (y1, z1) * (N₂ x.2).prob (y2, z2)))
  have hJ : Qf (wiretapJoint p (prodWiretap N₁ N₂)).prob
      = Qf (fun t : Fin n × (β₁ × β₂) × (γ₁ × γ₂) => ∑ x : α₁ × α₂,
          p.prob (t.1, x) * ((N₁ x.1).prob (t.2.1.1, t.2.2.1) * (N₂ x.2).prob (t.2.1.2, t.2.2.2))) :=
    rfl
  rw [hJ, hsplit]
  have hA : ∀ y1 : β₁, Qf (fun t : Fin n × β₂ × γ₂ => ∑ z1, ∑ x : α₁ × α₂,
        p.prob (t.1, x) * ((N₁ x.1).prob (y1, z1) * (N₂ x.2).prob (t.2.1, t.2.2)))
      ≤ (∑ t : Fin n × α₂, ∑ x1, p.prob (t.1, (x1, t.2)) * ∑ z1, (N₁ x1).prob (y1, z1))
          * privInfo N₂ := by
    intro y1
    have e : (fun t : Fin n × β₂ × γ₂ => ∑ z1, ∑ x : α₁ × α₂,
          p.prob (t.1, x) * ((N₁ x.1).prob (y1, z1) * (N₂ x.2).prob (t.2.1, t.2.2)))
        = (fun t : Fin n × β₂ × γ₂ => ∑ x2,
          (fun s : Fin n × α₂ => ∑ x1, p.prob (s.1, (x1, s.2)) * ∑ z1, (N₁ x1).prob (y1, z1))
            (t.1, x2) * (N₂ x2).prob t.2) := by
      funext t
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, Prod.mk.eta]
      rw [rev3]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => ?_
      ring
    rw [e]
    exact Qf_le N₂ (fun s : Fin n × α₂ => ∑ x1, p.prob (s.1, (x1, s.2)) * ∑ z1, (N₁ x1).prob (y1, z1)) (fun s => Finset.sum_nonneg fun x1 _ =>
      mul_nonneg (p.nonneg _) (Finset.sum_nonneg fun z1 _ => (N₁ x1).nonneg _))
  have hB : ∀ z2 : γ₂, Qf (fun t : Fin n × β₁ × γ₁ => ∑ y2, ∑ x : α₁ × α₂,
        p.prob (t.1, x) * ((N₁ x.1).prob (t.2.1, t.2.2) * (N₂ x.2).prob (y2, z2)))
      ≤ (∑ t : Fin n × α₁, ∑ x2, p.prob (t.1, (t.2, x2)) * ∑ y2, (N₂ x2).prob (y2, z2))
          * privInfo N₁ := by
    intro z2
    have e : (fun t : Fin n × β₁ × γ₁ => ∑ y2, ∑ x : α₁ × α₂,
          p.prob (t.1, x) * ((N₁ x.1).prob (t.2.1, t.2.2) * (N₂ x.2).prob (y2, z2)))
        = (fun t : Fin n × β₁ × γ₁ => ∑ x1,
          (fun s : Fin n × α₁ => ∑ x2, p.prob (s.1, (s.2, x2)) * ∑ y2, (N₂ x2).prob (y2, z2))
            (t.1, x1) * (N₁ x1).prob t.2) := by
      funext t
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, Prod.mk.eta]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun y2 _ => ?_
      ring
    rw [e]
    exact Qf_le N₁ (fun s : Fin n × α₁ => ∑ x2, p.prob (s.1, (s.2, x2)) * ∑ y2, (N₂ x2).prob (y2, z2)) (fun s => Finset.sum_nonneg fun x2 _ =>
      mul_nonneg (p.nonneg _) (Finset.sum_nonneg fun y2 _ => (N₂ x2).nonneg _))
  have hp : ∑ u, ∑ x1, ∑ x2, p.prob (u, (x1, x2)) = 1 := by
    have := p.sum_eq_one; simp only [Fintype.sum_prod_type] at this; exact this
  have hN1 : ∀ x1, ∑ y1, ∑ z1, (N₁ x1).prob (y1, z1) = 1 := fun x1 => by
    have := (N₁ x1).sum_eq_one; rwa [Fintype.sum_prod_type] at this
  have hN2 : ∀ x2, ∑ z2, ∑ y2, (N₂ x2).prob (y2, z2) = 1 := fun x2 => by
    rw [Finset.sum_comm]
    have := (N₂ x2).sum_eq_one; rwa [Fintype.sum_prod_type] at this
  have hGs : ∑ y1 : β₁, ∑ t : Fin n × α₂,
      ∑ x1, p.prob (t.1, (x1, t.2)) * ∑ z1, (N₁ x1).prob (y1, z1) = 1 := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm, ← hp]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm (f := fun x1 x2 => p.prob (u, (x1, x2)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x2 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [← Finset.mul_sum, hN1 x1, mul_one]
  have hHs : ∑ z2 : γ₂, ∑ t : Fin n × α₁,
      ∑ x2, p.prob (t.1, (t.2, x2)) * ∑ y2, (N₂ x2).prob (y2, z2) = 1 := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm, ← hp]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x2 _ => ?_
    rw [← Finset.mul_sum, hN2 x2, mul_one]
  refine (add_le_add (Finset.sum_le_sum fun y1 _ => hA y1)
    (Finset.sum_le_sum fun z2 _ => hB z2)).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, hGs, hHs]; ring

set_option maxHeartbeats 1000000 in
theorem ge_dir {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type} [Fintype α₁] [Fintype α₂] [Fintype β₁]
    [Fintype β₂] [Fintype γ₁] [Fintype γ₂] [Nonempty α₁] [Nonempty α₂]
    (N₁ : WiretapChannel α₁ β₁ γ₁) (N₂ : WiretapChannel α₂ β₂ γ₂) :
    privInfo N₁ + privInfo N₂ ≤ privInfo (prodWiretap N₁ N₂) := by
  have hb := bdd (prodWiretap N₁ N₂)
  have key : ∀ (n1 : ℕ) (p1 : FinDist (Fin n1 × α₁)) (n2 : ℕ) (p2 : FinDist (Fin n2 × α₂)),
      (mutualInfo (wiretapJoint p1 N₁).margXY - mutualInfo (wiretapJoint p1 N₁).margXZ)
      + (mutualInfo (wiretapJoint p2 N₂).margXY - mutualInfo (wiretapJoint p2 N₂).margXZ)
      ≤ privInfo (prodWiretap N₁ N₂) := by
    intro n1 p1 n2 p2
    let e : Fin (n1 * n2) ≃ Fin n1 × Fin n2 := finProdFinEquiv.symm
    let E : Fin (n1 * n2) × (α₁ × α₂) ≃ (Fin n1 × α₁) × (Fin n2 × α₂) :=
      (e.prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)
    let p : FinDist (Fin (n1 * n2) × (α₁ × α₂)) := (p1.prod p2).comap E
    have hJ : ∀ u y1 y2 z1 z2, (wiretapJoint p (prodWiretap N₁ N₂)).prob (u, (y1, y2), (z1, z2))
        = (wiretapJoint p1 N₁).prob ((e u).1, y1, z1)
          * (wiretapJoint p2 N₂).prob ((e u).2, y2, z2) := by
      intro u y1 y2 z1 z2
      show ∑ x : α₁ × α₂, p1.prob ((e u).1, x.1) * p2.prob ((e u).2, x.2)
          * ((N₁ x.1).prob (y1, z1) * (N₂ x.2).prob (y2, z2))
        = (∑ x1, p1.prob ((e u).1, x1) * (N₁ x1).prob (y1, z1))
          * (∑ x2, p2.prob ((e u).2, x2) * (N₂ x2).prob (y2, z2))
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ => ?_
      ring
    set J1 := (wiretapJoint p1 N₁).prob with hJ1
    set J2 := (wiretapJoint p2 N₂).prob with hJ2
    set J := (wiretapJoint p (prodWiretap N₁ N₂)).prob with hJdef
    have hUY : ∀ u y1 y2, ∑ z : γ₁ × γ₂, J (u, (y1, y2), z)
        = (∑ z1, J1 ((e u).1, y1, z1)) * (∑ z2, J2 ((e u).2, y2, z2)) := by
      intro u y1 y2
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => hJ u y1 y2 z1 z2
    have hUZ : ∀ u z1 z2, ∑ y : β₁ × β₂, J (u, y, (z1, z2))
        = (∑ y1, J1 ((e u).1, y1, z1)) * (∑ y2, J2 ((e u).2, y2, z2)) := by
      intro u z1 z2
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => hJ u y1 y2 z1 z2
    have hps : ∀ (F1 : Fin n1 → ℝ) (F2 : Fin n2 → ℝ),
        ∑ u, F1 (e u).1 * F2 (e u).2 = (∑ v1, F1 v1) * (∑ v2, F2 v2) := by
      intro F1 F2
      rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      exact Equiv.sum_comp e (fun v => F1 v.1 * F2 v.2)
    obtain ⟨a1, a2, a3, a4, -⟩ := msum J1
    obtain ⟨b1, b2, b3, b4, -⟩ := msum J2
    have t1 : ∑ t, J1 t = 1 := (wiretapJoint p1 N₁).sum_eq_one
    have t2 : ∑ t, J2 t = 1 := (wiretapJoint p2 N₂).sum_eq_one
    let EUY : Fin (n1 * n2) × (β₁ × β₂) ≃ (Fin n1 × β₁) × (Fin n2 × β₂) :=
      (e.prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)
    let EUZ : Fin (n1 * n2) × (γ₁ × γ₂) ≃ (Fin n1 × γ₁) × (Fin n2 × γ₂) :=
      (e.prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)
    have nUY : nl (fun uy : Fin (n1 * n2) × (β₁ × β₂) => ∑ z, J (uy.1, uy.2, z))
        = nl (fun w : Fin n1 × β₁ => ∑ z1, J1 (w.1, w.2, z1))
          + nl (fun w : Fin n2 × β₂ => ∑ z2, J2 (w.1, w.2, z2)) :=
      nl_tensor _ _ EUY _ (by rintro ⟨u, y1, y2⟩; exact hUY u y1 y2)
        (a1.trans t1) (b1.trans t2)
    have nUZ : nl (fun uz : Fin (n1 * n2) × (γ₁ × γ₂) => ∑ y, J (uz.1, y, uz.2))
        = nl (fun w : Fin n1 × γ₁ => ∑ y1, J1 (w.1, y1, w.2))
          + nl (fun w : Fin n2 × γ₂ => ∑ y2, J2 (w.1, y2, w.2)) :=
      nl_tensor _ _ EUZ _ (by rintro ⟨u, z1, z2⟩; exact hUZ u z1 z2)
        (a3.trans t1) (b3.trans t2)
    have nY : nl (fun y : β₁ × β₂ => ∑ u, ∑ z, J (u, y, z))
        = nl (fun y1 : β₁ => ∑ v1, ∑ z1, J1 (v1, y1, z1))
          + nl (fun y2 : β₂ => ∑ v2, ∑ z2, J2 (v2, y2, z2)) := by
      refine nl_tensor _ _ (Equiv.refl _) _ ?_ (a2.trans t1) (b2.trans t2)
      rintro ⟨y1, y2⟩
      show ∑ u, ∑ z, J (u, (y1, y2), z) = _
      rw [Finset.sum_congr rfl fun u _ => hUY u y1 y2]
      exact hps (fun v1 => ∑ z1, J1 (v1, y1, z1)) (fun v2 => ∑ z2, J2 (v2, y2, z2))
    have nZ : nl (fun z : γ₁ × γ₂ => ∑ u, ∑ y, J (u, y, z))
        = nl (fun z1 : γ₁ => ∑ v1, ∑ y1, J1 (v1, y1, z1))
          + nl (fun z2 : γ₂ => ∑ v2, ∑ y2, J2 (v2, y2, z2)) := by
      refine nl_tensor _ _ (Equiv.refl _) _ ?_ (a4.trans t1) (b4.trans t2)
      rintro ⟨z1, z2⟩
      show ∑ u, ∑ y, J (u, y, (z1, z2)) = _
      rw [Finset.sum_congr rfl fun u _ => hUZ u z1 z2]
      exact hps (fun v1 => ∑ y1, J1 (v1, y1, z1)) (fun v2 => ∑ y2, J2 (v2, y2, z2))
    have hQ : mutualInfo (wiretapJoint p (prodWiretap N₁ N₂)).margXY
          - mutualInfo (wiretapJoint p (prodWiretap N₁ N₂)).margXZ
        = (mutualInfo (wiretapJoint p1 N₁).margXY - mutualInfo (wiretapJoint p1 N₁).margXZ)
          + (mutualInfo (wiretapJoint p2 N₂).margXY - mutualInfo (wiretapJoint p2 N₂).margXZ) := by
      rw [Q_eq_Qf, Q_eq_Qf, Q_eq_Qf, ← hJ1, ← hJ2, ← hJdef]
      unfold Qf
      rw [nUY, nY, nUZ, nZ]; ring
    rw [← hQ]
    exact le_csSup hb ⟨n1 * n2, p, rfl⟩
  have h1 : privInfo N₁ ≤ privInfo (prodWiretap N₁ N₂) - privInfo N₂ := by
    apply csSup_le (setne N₁)
    rintro r ⟨n1, p1, rfl⟩
    rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
    apply csSup_le (setne N₂)
    rintro s ⟨n2, p2, rfl⟩
    rw [le_sub_iff_add_le, add_comm]
    exact key n1 p1 n2 p2
  linarith

end WildeQIT.PrivAdd

open WildeQIT WildeQIT.Wiretap in
theorem solution {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type} [Fintype α₁] [Fintype α₂] [Fintype β₁]
    [Fintype β₂] [Fintype γ₁] [Fintype γ₂] [Nonempty α₁] [Nonempty α₂]
    (N₁ : WiretapChannel α₁ β₁ γ₁) (N₂ : WiretapChannel α₂ β₂ γ₂) :
    privInfo (prodWiretap N₁ N₂) = privInfo N₁ + privInfo N₂ := by
  exact le_antisymm (WildeQIT.PrivAdd.le_dir N₁ N₂) (WildeQIT.PrivAdd.ge_dir N₁ N₂)
