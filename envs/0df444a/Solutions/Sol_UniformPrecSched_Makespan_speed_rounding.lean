-- Prove2me | solution 1 for UniformPrecSched.Makespan.speed_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T05:00:46.782986+00:00
-- url     : https://prove2.me/submissions/a70ecf13-3c4e-4fd2-b8d8-0aa2bdab8d2f

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP
import Definitions.Def_UniformPrecSched_Makespan_Rounding

set_option autoImplicit false

open UniformPrecSched.Makespan in
theorem SR.classSpeed_mem {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    ∃ i, I.s i = classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := Finset.orderEmbOfFin_mem _ _ _
  simpa [speedSet] using h

open UniformPrecSched.Makespan in
theorem SR.classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  obtain ⟨i, hi⟩ := SR.classSpeed_mem I κ
  rw [← hi]; exact I.s_pos i

open UniformPrecSched.Makespan in
theorem SR.classCount_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classCount I κ := by
  obtain ⟨i, hi⟩ := SR.classSpeed_mem I κ
  unfold classCount
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

open UniformPrecSched.Makespan in
theorem SR.exists_class {n m : ℕ} (I : Instance n m) (i : Fin m) :
    ∃ κ, classSpeed I κ = I.s i := by
  have h : I.s i ∈ Set.range ((speedSet I).orderEmbOfFin
      (rfl : (speedSet I).card = numSpeeds I)) := by
    rw [Finset.range_orderEmbOfFin]; simp [speedSet]
  obtain ⟨κ', hκ'⟩ := h
  exact ⟨Fin.rev κ', (congrArg ((speedSet I).orderEmbOfFin rfl) (Fin.rev_rev κ')).trans hκ'⟩

open UniformPrecSched.Makespan in
theorem SR.classSpeed_inj {n m : ℕ} (I : Instance n m) :
    Function.Injective (classSpeed I) := by
  intro a b h
  unfold classSpeed at h
  exact Fin.rev_injective (((speedSet I).orderEmbOfFin rfl).injective h)

open UniformPrecSched.Makespan in
theorem SR.le_maxSpeed {n m : ℕ} (I : Instance n m) (i : Fin m) : I.s i ≤ maxSpeed I :=
  Finset.le_sup' I.s (Finset.mem_univ i)

open UniformPrecSched.Makespan in
theorem SR.classSpeed_le_max {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    classSpeed I κ ≤ maxSpeed I := by
  obtain ⟨i, hi⟩ := SR.classSpeed_mem I κ
  rw [← hi]; exact SR.le_maxSpeed I i

open UniformPrecSched.Makespan in
theorem SR.le_beta_rounded {n m : ℕ} (I : Instance n m) {β v : ℝ} (hβ : 1 < β) (hv : 0 < v) :
    v ≤ β * roundedSpeed I β v := by
  unfold roundedSpeed
  have hM := maxSpeed_pos I
  set x : ℝ := Real.logb β (maxSpeed I / v) with hx
  have hβ0 : 0 < β := by linarith
  have h1 : β ^ (-(⌊x⌋ + 1)) = β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    push_cast
    ring_nf
  rw [h1]
  have h2 : β ^ (-(x + 1)) ≤ β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hβ.le
    push_cast
    linarith [Int.floor_le x]
  have h3 : β ^ (-(x + 1)) = v / maxSpeed I / β := by
    rw [neg_add, Real.rpow_add hβ0, Real.rpow_neg hβ0.le, hx,
      Real.rpow_logb hβ0 hβ.ne' (div_pos hM hv), inv_div, Real.rpow_neg_one, div_eq_mul_inv _ β]
  rw [h3] at h2
  calc v = β * (maxSpeed I * (v / maxSpeed I / β)) := by field_simp
    _ ≤ β * (maxSpeed I * β ^ (-(((⌊x⌋ + 1 : ℤ) : ℝ)))) := by gcongr

open UniformPrecSched.Makespan in
theorem SR.kept_preimage {n m : ℕ} (I : Instance n m) (α : ℝ) {i : Fin m}
    (h : maxSpeed I / (α * m) ≤ I.s i) : ∃ i', keptEmb I α i' = i := by
  have hr := Finset.range_orderEmbOfFin (keptSet I α) (rfl : (keptSet I α).card = keptCount I α)
  have : i ∈ Set.range ((keptSet I α).orderEmbOfFin
      (rfl : (keptSet I α).card = keptCount I α)) := by
    rw [hr]; simp [keptSet, h]
  exact this

open UniformPrecSched.Makespan in
theorem SR.kept_of {n m : ℕ} (I : Instance n m) (α : ℝ) (i' : Fin (keptCount I α)) :
    maxSpeed I / (α * m) ≤ I.s (keptEmb I α i') := by
  have h : keptEmb I α i' ∈ keptSet I α := Finset.orderEmbOfFin_mem _ _ _
  unfold keptSet at h
  exact (Finset.mem_filter.mp h).2

open UniformPrecSched.Makespan in
theorem SR.machine_sum {n m : ℕ} (I : Instance n m) (c : Fin m → Fin (numSpeeds I))
    (hc : ∀ i, classSpeed I (c i) = I.s i) (F : Fin (numSpeeds I) → ℝ) :
    ∑ κ, (classCount I κ : ℝ) * F κ = ∑ i, F (c i) := by
  classical
  have key : ∀ κ, (classCount I κ : ℝ) * F κ =
      ∑ i ∈ Finset.univ.filter (fun i => c i = κ), F (c i) := by
    intro κ
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
    unfold classCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hc i]
    exact (SR.classSpeed_inj I).eq_iff
  rw [Finset.sum_congr rfl (fun κ _ => key κ)]
  exact Finset.sum_fiberwise _ _ _

open UniformPrecSched.Makespan in
theorem SR.num_part {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β) :
    (numSpeeds (roundInstance I α β hα hβ) : ℝ) ≤ (⌊Real.logb β (α * m)⌋ : ℝ) + 1 := by
  classical
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast I.m_pos
  have ham : (1 : ℝ) ≤ α * m := by nlinarith
  have hampos : (0 : ℝ) < α * m := by linarith
  have hL : 0 ≤ Real.logb β (α * m) := Real.logb_nonneg hβ ham
  have hN : 0 ≤ ⌊Real.logb β (α * m)⌋ := Int.floor_nonneg.mpr hL
  have hsub : speedSet (roundInstance I α β hα hβ) ⊆
      (Finset.Icc (0 : ℤ) ⌊Real.logb β (α * m)⌋).image
        (fun k : ℤ => maxSpeed I * β ^ (-(k + 1))) := by
    intro u hu
    simp only [speedSet, Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨i', rfl⟩ := hu
    have hk := SR.kept_of I α i'
    have hs := I.s_pos (keptEmb I α i')
    have hle := SR.le_maxSpeed I (keptEmb I α i')
    refine Finset.mem_image.mpr ⟨⌊Real.logb β (maxSpeed I / I.s (keptEmb I α i'))⌋,
      Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Int.floor_nonneg.mpr (Real.logb_nonneg hβ ((one_le_div hs).mpr hle))
    · apply Int.floor_mono
      apply Real.logb_le_logb_of_le hβ (div_pos (maxSpeed_pos I) hs)
      rw [div_le_iff₀ hs]
      rw [div_le_iff₀ hampos] at hk
      linarith
  have hcard : numSpeeds (roundInstance I α β hα hβ) ≤ (⌊Real.logb β (α * m)⌋ + 1).toNat := by
    unfold numSpeeds
    calc (speedSet (roundInstance I α β hα hβ)).card
        ≤ ((Finset.Icc (0 : ℤ) ⌊Real.logb β (α * m)⌋).image
            (fun k : ℤ => maxSpeed I * β ^ (-(k + 1)))).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc (0 : ℤ) ⌊Real.logb β (α * m)⌋).card := Finset.card_image_le
      _ = (⌊Real.logb β (α * m)⌋ + 1).toNat := by rw [Int.card_Icc]; congr 1; ring
  have hz : (numSpeeds (roundInstance I α β hα hβ) : ℤ) ≤ ⌊Real.logb β (α * m)⌋ + 1 := by
    have := (Int.ofNat_le.mpr hcard)
    rw [Int.toNat_of_nonneg (by linarith)] at this
    exact this
  exact_mod_cast hz

open UniformPrecSched.Makespan in
noncomputable def SR.tgt {n m : ℕ} (I : Instance n m) (α β v : ℝ) : ℝ :=
  if maxSpeed I / (α * m) ≤ v then roundedSpeed I β v else roundedSpeed I β (maxSpeed I)

open UniformPrecSched.Makespan in
theorem SR.lp_part {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β) :
    ∀ x C D, LPFeasible I x C D →
      ∃ x' C' D', LPFeasible (roundInstance I α β hα hβ) x' C' D' ∧
        D' ≤ β * (1 + 1 / α) * D := by
  classical
  rintro x C D ⟨h1, h2, h3, h4, h5, h8⟩
  have hβ0 : 0 < β := by linarith
  have hα0 : 0 < α := by linarith
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast I.m_pos
  have ham : (1 : ℝ) ≤ α * m := by nlinarith
  have hampos : (0 : ℝ) < α * m := by linarith
  set I' := roundInstance I α β hα hβ with hI'
  choose c hc using SR.exists_class I
  have hkeptcls : ∀ i, maxSpeed I / (α * m) ≤ I.s i →
      ∃ κ', classSpeed I' κ' = roundedSpeed I β (I.s i) := by
    intro i hi
    obtain ⟨i', rfl⟩ := SR.kept_preimage I α hi
    obtain ⟨κ', hκ'⟩ := SR.exists_class I' i'
    exact ⟨κ', hκ'⟩
  have ht : ∀ κ, ∃ κ', classSpeed I' κ' = SR.tgt I α β (classSpeed I κ) := by
    intro κ
    unfold SR.tgt
    split_ifs with hk
    · obtain ⟨i, hi⟩ := SR.classSpeed_mem I κ
      rw [← hi] at hk ⊢
      exact hkeptcls i hk
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (machines_nonempty I) I.s
      have hi0' : maxSpeed I = I.s i0 := hi0
      rw [hi0']
      apply hkeptcls i0
      rw [← hi0']
      exact div_le_self (maxSpeed_pos I).le ham
  choose f hf using ht
  have hvt : ∀ κ, classSpeed I κ ≤ β * SR.tgt I α β (classSpeed I κ) := by
    intro κ
    unfold SR.tgt
    split_ifs
    · exact SR.le_beta_rounded I hβ (SR.classSpeed_pos I κ)
    · exact (SR.classSpeed_le_max I κ).trans (SR.le_beta_rounded I hβ (maxSpeed_pos I))
  have hD : 0 ≤ D := by
    have h := h2 (c ⟨0, I.m_pos⟩)
    refine le_trans ?_ h
    apply mul_nonneg
    · have := SR.classCount_pos I (c ⟨0, I.m_pos⟩)
      have := SR.classSpeed_pos I (c ⟨0, I.m_pos⟩)
      positivity
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (I.p_pos j).le (h8 _ j))
  have hpb : ∀ j, ∑ κ', I.p j / classSpeed I' κ' *
      (∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j) ≤
      β * ∑ κ, I.p j / classSpeed I κ * x κ j := by
    intro j
    calc ∑ κ', I.p j / classSpeed I' κ' *
          (∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j)
        = ∑ κ', ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'),
            I.p j / classSpeed I' (f κ) * x κ j := by
          refine Finset.sum_congr rfl (fun κ' _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun κ hκ => ?_)
          rw [(Finset.mem_filter.mp hκ).2]
      _ = ∑ κ, I.p j / classSpeed I' (f κ) * x κ j := Finset.sum_fiberwise _ _ _
      _ ≤ ∑ κ, β * (I.p j / classSpeed I κ * x κ j) := by
          apply Finset.sum_le_sum
          intro κ _
          rw [hf κ]
          have hv := SR.classSpeed_pos I κ
          have hle : classSpeed I κ / β ≤ SR.tgt I α β (classSpeed I κ) := by
            rw [div_le_iff₀ hβ0]; linarith [hvt κ]
          have hq : I.p j / SR.tgt I α β (classSpeed I κ) ≤ I.p j / (classSpeed I κ / β) :=
            div_le_div_of_nonneg_left (I.p_pos j).le (div_pos hv hβ0) hle
          rw [div_div_eq_mul_div] at hq
          calc I.p j / SR.tgt I α β (classSpeed I κ) * x κ j
              ≤ I.p j * β / classSpeed I κ * x κ j :=
                mul_le_mul_of_nonneg_right hq (h8 κ j)
            _ = β * (I.p j / classSpeed I κ * x κ j) := by ring
      _ = β * ∑ κ, I.p j / classSpeed I κ * x κ j := (Finset.mul_sum _ _ _).symm
  refine ⟨fun κ' j => ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j,
    fun j => β * C j, β * (1 + 1 / α) * D, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, le_rfl⟩
  · intro j
    show ∑ κ', ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j = 1
    rw [Finset.sum_fiberwise]
    exact h1 j
  · intro κ'
    show (1 / ((classCount I' κ' : ℝ) * classSpeed I' κ')) *
      ∑ j, I.p j * ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j ≤ β * (1 + 1 / α) * D
    have hs' := SR.classSpeed_pos I' κ'
    have hm'n := SR.classCount_pos I' κ'
    have hm' : (1 : ℝ) ≤ (classCount I' κ' : ℝ) := by exact_mod_cast hm'n
    -- step a
    have ha : ∑ j, I.p j * ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j =
        ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), ∑ j, I.p j * x κ j := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    -- step b
    have hb : ∀ κ, ∑ j, I.p j * x κ j ≤ ((classCount I κ : ℝ) * classSpeed I κ) * D := by
      intro κ
      have h := h2 κ
      have hpos : (0 : ℝ) < (classCount I κ : ℝ) * classSpeed I κ := by
        have := SR.classCount_pos I κ
        have := SR.classSpeed_pos I κ
        positivity
      rwa [one_div, inv_mul_le_iff₀ hpos] at h
    -- step c
    have hc2 : ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'),
        (classCount I κ : ℝ) * classSpeed I κ =
        ∑ i ∈ Finset.univ.filter (fun i => f (c i) = κ'), I.s i := by
      rw [Finset.sum_filter, Finset.sum_filter]
      calc ∑ κ, (if f κ = κ' then (classCount I κ : ℝ) * classSpeed I κ else 0)
          = ∑ κ, (classCount I κ : ℝ) * (if f κ = κ' then classSpeed I κ else 0) := by
            refine Finset.sum_congr rfl (fun κ _ => ?_)
            split_ifs <;> simp
        _ = ∑ i, (if f (c i) = κ' then classSpeed I (c i) else 0) :=
            SR.machine_sum I c hc _
        _ = ∑ i, (if f (c i) = κ' then I.s i else 0) := by simp only [hc]
    -- every machine in the fibre has speed at most β s'
    have hpt : ∀ i, f (c i) = κ' → I.s i ≤ β * classSpeed I' κ' := by
      intro i hi
      rw [← hi, hf (c i), ← hc i]
      exact hvt (c i)
    -- step e: kept part
    have he : ∑ i ∈ (Finset.univ.filter (fun i => f (c i) = κ')).filter
        (fun i => maxSpeed I / (α * m) ≤ I.s i), I.s i ≤
        (classCount I' κ' : ℝ) * (β * classSpeed I' κ') := by
      have hsum := Finset.sum_le_card_nsmul
        ((Finset.univ.filter (fun i => f (c i) = κ')).filter
          (fun i => maxSpeed I / (α * m) ≤ I.s i)) I.s (β * classSpeed I' κ')
        (fun i hi => hpt i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
      rw [nsmul_eq_mul] at hsum
      refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have hsub : (Finset.univ.filter (fun i => f (c i) = κ')).filter
          (fun i => maxSpeed I / (α * m) ≤ I.s i) ⊆
          (Finset.univ.filter (fun i' => I'.s i' = classSpeed I' κ')).image (keptEmb I α) := by
        intro i hi
        obtain ⟨hi1, hk⟩ := Finset.mem_filter.mp hi
        have hfi := (Finset.mem_filter.mp hi1).2
        obtain ⟨i', rfl⟩ := SR.kept_preimage I α hk
        refine Finset.mem_image.mpr ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        rw [← hfi, hf (c _)]
        unfold SR.tgt
        rw [hc, if_pos hk]
        rfl
      have hcd := (Finset.card_le_card hsub).trans Finset.card_image_le
      have : (Finset.univ.filter (fun i' => I'.s i' = classSpeed I' κ')).card =
          classCount I' κ' := by
        unfold classCount; rfl
      rw [this] at hcd
      exact_mod_cast hcd
    -- step f: dropped part
    have hf2 : ∑ i ∈ (Finset.univ.filter (fun i => f (c i) = κ')).filter
        (fun i => ¬ maxSpeed I / (α * m) ≤ I.s i), I.s i ≤
        (m : ℝ) * (β * classSpeed I' κ' / (α * m)) := by
      have hsum := Finset.sum_le_card_nsmul
        ((Finset.univ.filter (fun i => f (c i) = κ')).filter
          (fun i => ¬ maxSpeed I / (α * m) ≤ I.s i)) I.s (β * classSpeed I' κ' / (α * m))
        (by
          intro i hi
          obtain ⟨hi1, hk⟩ := Finset.mem_filter.mp hi
          have hfi := (Finset.mem_filter.mp hi1).2
          have hs'eq : classSpeed I' κ' = roundedSpeed I β (maxSpeed I) := by
            rw [← hfi, hf (c i)]
            unfold SR.tgt
            rw [hc, if_neg hk]
          have hmb := SR.le_beta_rounded I hβ (maxSpeed_pos I)
          rw [← hs'eq] at hmb
          rw [not_le] at hk
          calc I.s i ≤ maxSpeed I / (α * m) := hk.le
            _ ≤ β * classSpeed I' κ' / (α * m) := by gcongr)
      rw [nsmul_eq_mul] at hsum
      refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := Finset.card_le_univ ((Finset.univ.filter (fun i => f (c i) = κ')).filter
          (fun i => ¬ maxSpeed I / (α * m) ≤ I.s i))
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun i => f (c i) = κ')) (fun i => maxSpeed I / (α * m) ≤ I.s i) I.s
    have hmid : (m : ℝ) * (β * classSpeed I' κ' / (α * m)) = β * classSpeed I' κ' * (1 / α) := by
      field_simp
    have hA : ∑ j, I.p j * ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j ≤
        D * ((classCount I' κ' : ℝ) * (β * classSpeed I' κ') + β * classSpeed I' κ' * (1 / α)) := by
      rw [ha]
      calc ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), ∑ j, I.p j * x κ j
          ≤ ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'),
              ((classCount I κ : ℝ) * classSpeed I κ) * D :=
            Finset.sum_le_sum (fun κ _ => hb κ)
        _ = D * ∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'),
              (classCount I κ : ℝ) * classSpeed I κ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ ≤ _ := by
            rw [hc2, ← hsplit]
            apply mul_le_mul_of_nonneg_left _ hD
            linarith
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    have key : 0 ≤ D * β * classSpeed I' κ' * ((classCount I' κ' : ℝ) - 1) * (1 / α) := by
      have : (0 : ℝ) ≤ (classCount I' κ' : ℝ) - 1 := by linarith
      have : (0 : ℝ) ≤ 1 / α := by positivity
      have : 0 ≤ D * β := mul_nonneg hD hβ0.le
      have : 0 ≤ D * β * classSpeed I' κ' := mul_nonneg this hs'.le
      positivity
    have e : (classCount I' κ' : ℝ) * classSpeed I' κ' * (β * (1 + 1 / α) * D) -
        D * ((classCount I' κ' : ℝ) * (β * classSpeed I' κ') + β * classSpeed I' κ' * (1 / α)) =
        D * β * classSpeed I' κ' * ((classCount I' κ' : ℝ) - 1) * (1 / α) := by ring
    linarith
  · intro j
    show ∑ κ', I.p j / classSpeed I' κ' *
      (∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j) ≤ β * C j
    exact (hpb j).trans (mul_le_mul_of_nonneg_left (h3 j) hβ0.le)
  · intro j' j hp
    show ∑ κ', I.p j / classSpeed I' κ' *
      (∑ κ ∈ Finset.univ.filter (fun κ => f κ = κ'), x κ j) ≤ β * C j - β * C j'
    have := h4 j' j hp
    have h' := mul_le_mul_of_nonneg_left this hβ0.le
    linarith [hpb j]
  · intro j
    show β * C j ≤ β * (1 + 1 / α) * D
    have hCD := mul_le_mul_of_nonneg_left (h5 j) hβ0.le
    have h1a : 0 ≤ β * (1 / α) * D := by positivity
    have e : β * (1 + 1 / α) * D = β * D + β * (1 / α) * D := by ring
    linarith
  · intro κ' j
    exact Finset.sum_nonneg (fun κ _ => h8 κ j)

open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β) :
    (numSpeeds (roundInstance I α β hα hβ) : ℝ) ≤ (⌊Real.logb β (α * m)⌋ : ℝ) + 1 ∧
      ∀ x C D, LPFeasible I x C D →
        ∃ x' C' D', LPFeasible (roundInstance I α β hα hβ) x' C' D' ∧
          D' ≤ β * (1 + 1 / α) * D := by
  exact ⟨SR.num_part I α β hα hβ, SR.lp_part I α β hα hβ⟩
