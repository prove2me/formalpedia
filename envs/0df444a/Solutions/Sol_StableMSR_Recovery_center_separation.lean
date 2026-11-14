-- Prove2me | solution 1 for StableMSR.Recovery.center_separation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:18:34.003218+00:00
-- url     : https://prove2.me/submissions/94b31041-4e85-4b8b-a7de-7123d86a1504

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace CenterAux

lemma radius_le_ecc {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : c ∈ C) :
    radius d C ≤ eccentricity d C c := by
  classical
  rw [radius, dif_pos ⟨c, hc⟩]
  exact Finset.inf'_le _ hc

lemma dist_le_ecc {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (c : Point n) {x : Point n} (hx : x ∈ C) :
    d c x ≤ eccentricity d C c := by
  classical
  rw [eccentricity, dif_pos ⟨x, hx⟩]
  exact Finset.le_sup' _ hx

lemma ecc_le {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) (c : Point n) {a : ℝ}
    (ha : ∀ x ∈ C, d c x ≤ a) : eccentricity d C c ≤ a := by
  classical
  rw [eccentricity, dif_pos hC]
  exact Finset.sup'_le hC _ ha

lemma ecc_le_iff {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) (c : Point n) (a : ℝ) :
    eccentricity d C c ≤ a ↔ ∀ x ∈ C, d c x ≤ a := by
  constructor
  · intro h x hx
    exact (dist_le_ecc d c hx).trans h
  · exact ecc_le d hC c

lemma radius_le {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : c ∈ C) {a : ℝ}
    (ha : ∀ x ∈ C, d c x ≤ a) : radius d C ≤ a :=
  (radius_le_ecc d hc).trans (ecc_le d ⟨c, hc⟩ c ha)

lemma le_radius {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ c ∈ C, a ≤ eccentricity d C c) : a ≤ radius d C := by
  classical
  rw [radius, dif_pos hC]
  exact Finset.le_inf' hC _ ha

lemma exists_optimal_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, heq⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using heq.symm⟩

lemma exists_far {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {x : Point n} (hx : x ∈ C) :
    ∃ y ∈ C, radius d C ≤ d x y := by
  classical
  have hC : C.Nonempty := ⟨x, hx⟩
  obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_sup' hC (d x)
  refine ⟨y, hy, ?_⟩
  have h := radius_le_ecc d hx
  simpa [eccentricity, hC, heq] using h

lemma radius_pos {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) {C : Cluster n} (hC : 2 ≤ C.card) :
    0 < radius d C := by
  classical
  have hC' : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc, hecc⟩ := exists_optimal_center d hC'
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hcy : 0 < d c y := by
    rw [← hm c y]
    exact dist_pos.mpr (Ne.symm hyc)
  exact lt_of_lt_of_le hcy ((dist_le_ecc d c hy).trans hecc.le)

end CenterAux


namespace CenterAux

lemma metric_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_nonneg

lemma metric_symm {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm]
  exact dist_comm x y

lemma metric_triangle {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm, ← hm]
  exact dist_triangle x y z

lemma metric_self {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x : Point n) : d x x = 0 := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_self x

lemma metric_pos {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {x y : Point n} (hxy : x ≠ y) : 0 < d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_pos.mpr hxy

lemma dist_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := (dist_le_ecc d c hx).trans hc.2.le

lemma radius_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) : 0 ≤ radius d C := by
  obtain ⟨c, hc⟩ := exists_optimal_center d hC
  exact (metric_nonneg hd c c).trans (dist_le_radius hc hc.1)

lemma radius_singleton {n : ℕ} (d : Point n → Point n → ℝ) (x : Point n) :
    radius d {x} = d x x := by
  classical
  simp [radius, eccentricity]

lemma radius_scale_on {n : ℕ} (d e : Point n → Point n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    {A : Cluster n} (hA : A.Nonempty)
    (hscale : ∀ x ∈ A, ∀ y ∈ A, e x y = a * d x y) :
    radius e A = a * radius d A := by
  apply le_antisymm
  · obtain ⟨c, hc⟩ := exists_optimal_center d hA
    apply radius_le e hc.1
    intro x hx
    rw [hscale c hc.1 x hx]
    exact mul_le_mul_of_nonneg_left (dist_le_radius hc hx) ha
  · apply le_radius e hA
    intro c hc
    obtain ⟨y, hy, hcy⟩ := exists_far d hc
    have h := mul_le_mul_of_nonneg_left hcy ha
    rw [← hscale c hc y hy] at h
    exact h.trans (dist_le_ecc e c hy)

lemma competitor_impossible {n k : ℕ} {d : Point n → Point n → ℝ}
    {O Q : Partition n} (hO : UniqueOptimal d Finset.univ k O)
    (hQ : Feasible Finset.univ k Q) (hne : Q ≠ O) (hle : cost d Q ≤ cost d O) : False := by
  apply hne
  apply hO.2 Q
  refine ⟨hQ, ?_⟩
  intro R hR
  exact hle.trans (hO.1.2 R hR)

end CenterAux

namespace CenterAux

lemma mixed_block_not_mem {n k : ℕ} {O : Partition n}
    (hO : Feasible Finset.univ k O) {C D A : Cluster n}
    (hC : C ∈ O) (hD : D ∈ O) (hCD : C ≠ D)
    {x y : Point n} (hxA : x ∈ A) (hxC : x ∈ C) (hyA : y ∈ A) (hyD : y ∈ D) :
    A ∉ O := by
  intro hA
  have hAC : A = C := by
    by_contra hn
    exact Finset.disjoint_left.mp (hO.2.2.1 hA hC hn) hxA hxC
  have hAD : A = D := by
    by_contra hn
    exact Finset.disjoint_left.mp (hO.2.2.1 hA hD hn) hyA hyD
  exact hCD (hAC.symm.trans hAD)

lemma replace_two {n k : ℕ} (O : Partition n) (C D A B : Cluster n)
    (hO : Feasible Finset.univ k O) (hC : C ∈ O) (hD : D ∈ O) (hCD : C ≠ D)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hcover : A ∪ B = C ∪ D) (hAnO : A ∉ O) :
    ∃ Q : Partition n, Feasible Finset.univ k Q ∧ Q ≠ O ∧
      ∀ w : Cluster n → ℝ,
        (∑ X ∈ Q, w X) = (∑ X ∈ O \ {C, D}, w X) + w A + w B ∧
        (∑ X ∈ O, w X) = (∑ X ∈ O \ {C, D}, w X) + w C + w D := by
  classical
  let R := O \ {C, D}
  let S : Partition n := {A, B}
  have hsub : ({C, D} : Partition n) ⊆ O := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hC, hD⟩
  have hRsub : R ⊆ O := Finset.sdiff_subset
  have hOunion : R ∪ {C, D} = O := Finset.sdiff_union_of_subset hsub
  have hABne : A ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := hA
    exact Finset.disjoint_left.mp hAB hx (heq ▸ hx)
  have hRout : ∀ X ∈ R, Disjoint X (C ∪ D) := by
    intro X hX
    obtain ⟨hXO, hXn⟩ := Finset.mem_sdiff.mp hX
    have hXC : X ≠ C := by intro h; exact hXn (by simp [h])
    have hXD : X ≠ D := by intro h; exact hXn (by simp [h])
    exact Finset.disjoint_union_right.mpr ⟨hO.2.2.1 hXO hC hXC, hO.2.2.1 hXO hD hXD⟩
  have hASub : A ⊆ C ∪ D := by rw [← hcover]; exact Finset.subset_union_left
  have hBSub : B ⊆ C ∪ D := by rw [← hcover]; exact Finset.subset_union_right
  have hRSA : ∀ X ∈ R, Disjoint X A := fun X hX => (hRout X hX).mono_right hASub
  have hRSB : ∀ X ∈ R, Disjoint X B := fun X hX => (hRout X hX).mono_right hBSub
  have hRSdisj : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro X hXR hXS
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hXS
    rcases hXS with rfl | rfl
    · exact hAnO (hRsub hXR)
    · obtain ⟨x, hx⟩ := hB
      exact Finset.disjoint_left.mp (hRSB _ hXR) hx hx
  let Q := R ∪ S
  have hQfeas : Feasible Finset.univ k Q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (R ∪ S).card = k
      rw [Finset.card_union_of_disjoint hRSdisj]
      have hcard : R.card + ({C, D} : Partition n).card = k := by
        rw [← Finset.card_union_of_disjoint (Finset.sdiff_disjoint : Disjoint R {C, D}), hOunion]
        exact hO.1
      simpa [S, hABne, hCD] using hcard
    · intro X hX
      rcases Finset.mem_union.mp hX with hXR | hXS
      · exact hO.2.1 X (hRsub hXR)
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hXS
        rcases hXS with rfl | rfl
        · exact hA
        · exact hB
    · intro X hX Y hY hXY
      rcases Finset.mem_union.mp hX with hXR | hXS <;>
        rcases Finset.mem_union.mp hY with hYR | hYS
      · exact hO.2.2.1 (hRsub hXR) (hRsub hYR) hXY
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hYS
        rcases hYS with rfl | rfl
        · exact hRSA X hXR
        · exact hRSB X hXR
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hXS
        rcases hXS with rfl | rfl
        · exact (hRSA Y hYR).symm
        · exact (hRSB Y hYR).symm
      · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hXS hYS
        rcases hXS with rfl | rfl <;> rcases hYS with rfl | rfl
        · exact False.elim (hXY rfl)
        · exact hAB
        · exact hAB.symm
        · exact False.elim (hXY rfl)
    · change (R ∪ S).biUnion id = Finset.univ
      rw [Finset.union_biUnion]
      have hScov : S.biUnion id = C ∪ D := by simp [S, hcover]
      rw [hScov]
      have hOc : (R ∪ ({C, D} : Partition n)).biUnion id = Finset.univ := by
        rw [hOunion]; exact hO.2.2.2
      simpa [Finset.union_biUnion, Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using hOc
  have hQne : Q ≠ O := by
    intro heq
    apply hAnO
    rw [← heq]
    exact Finset.mem_union_right R (by simp [S])
  refine ⟨Q, hQfeas, hQne, ?_⟩
  intro w
  constructor
  · change (∑ X ∈ R ∪ S, w X) = _
    rw [Finset.sum_union hRSdisj]
    simp only [S, Finset.sum_pair hABne]
    ring
  · have hsum : (∑ X ∈ O, w X) = (∑ X ∈ R, w X) + ∑ X ∈ ({C, D} : Partition n), w X := by
      rw [← Finset.sum_union (Finset.sdiff_disjoint : Disjoint R {C, D}), hOunion]
    rw [hsum]
    simp only [Finset.sum_pair hCD]
    ring

end CenterAux

namespace CenterAux

lemma point_separation {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (C : Cluster n) (hC : C ∈ O) (c : Point n) (hc : OptimalCenter d C c) :
    ∀ p : Point n, p ∉ C → γ * radius d C < d c p := by
  classical
  intro p hp
  by_contra hn
  have hcp : d c p ≤ γ * radius d C := le_of_not_gt hn
  have hpc : p ≠ c := by intro h; exact hp (h ▸ hc.1)
  have hrC : 0 < radius d C := by
    have hpos := metric_pos hd (Ne.symm hpc)
    have hγ0 : 0 < γ := by linarith
    nlinarith
  have hγ0 : 0 ≤ γ := by linarith
  have hpU : p ∈ O.biUnion id := by rw [hO.1.2.2.2]; simp
  obtain ⟨D, hD, hpD⟩ := Finset.mem_biUnion.mp hpU
  change p ∈ D at hpD
  have hCD : C ≠ D := by intro heq; exact hp (heq ▸ hpD)
  have hCDdis : Disjoint C D := hO.1.2.2.1 hC hD hCD
  have hcD : c ∉ D := fun h => Finset.disjoint_left.mp hCDdis hc.1 h
  have hCn : C.Nonempty := hO.1.2.1 C hC
  have hDn : D.Nonempty := hO.1.2.1 D hD
  let P : Point n → Point n → Prop := fun x y => (x = c ∧ y ∈ D) ∨ (y = c ∧ x ∈ D)
  have hPsymm : ∀ x y, P x y ↔ P y x := by intro x y; dsimp [P]; exact or_comm
  let e : Point n → Point n → ℝ := fun x y => if P x y then d x y else γ * d x y
  have hebound : ∀ x y, d x y ≤ e x y ∧ e x y ≤ γ * d x y := by
    intro x y
    have hs : d x y ≤ γ * d x y := by nlinarith [metric_nonneg hd x y]
    dsimp [e]
    split_ifs <;> exact ⟨by first | exact hs | rfl, by first | exact hs | rfl⟩
  have he : Perturbation d γ e := by
    refine ⟨?_, hebound⟩
    intro x y
    simp only [e, hPsymm x y, metric_symm hd x y]
  have hediag : ∀ x, e x x = 0 := by
    intro x
    have h := hebound x x
    rw [metric_self hd x, mul_zero] at h
    exact le_antisymm h.2 h.1
  have hec : ∀ y ∈ D, e c y = d c y := by
    intro y hy
    have hP : P c y := Or.inl ⟨rfl, hy⟩
    simp only [e, if_pos hP]
  have heC : ∀ x ∈ C, ∀ y ∈ C, e x y = γ * d x y := by
    intro x hx y hy
    have hnP : ¬ P x y := by
      rintro (⟨hxc, hyD⟩ | ⟨hyc, hxD⟩)
      · exact Finset.disjoint_left.mp hCDdis hy hyD
      · exact Finset.disjoint_left.mp hCDdis hx hxD
    simp only [e, if_neg hnP]
  have heD : ∀ x ∈ D, ∀ y ∈ D, e x y = γ * d x y := by
    intro x hx y hy
    have hnP : ¬ P x y := by
      rintro (⟨hxc, hyD⟩ | ⟨hyc, hxD⟩)
      · exact hcD (hxc ▸ hx)
      · exact hcD (hyc ▸ hy)
    simp only [e, if_neg hnP]
  have hrCe : radius e C = γ * radius d C := radius_scale_on d e γ hγ0 hCn heC
  have hrDe : radius e D = γ * radius d D := radius_scale_on d e γ hγ0 hDn heD
  have hbad : ∀ A B : Cluster n, A.Nonempty → B.Nonempty → Disjoint A B →
      A ∪ B = C ∪ D → A ∉ O →
      radius e A + radius e B ≤ γ * radius d C + γ * radius d D → False := by
    intro A B hA hB hAB hcover hAnO hcost
    obtain ⟨Q, hQ, hQne, hsum⟩ := replace_two O C D A B hO.1 hC hD hCD hA hB hAB hcover hAnO
    obtain ⟨hQsum, hOsum⟩ := hsum (radius e)
    change cost e Q = _ at hQsum
    change cost e O = _ at hOsum
    rw [hrCe, hrDe] at hOsum
    apply competitor_impossible (hO.2 e he) hQ hQne
    linarith
  by_cases hDsingle : D = {p}
  · obtain ⟨x, hx, hfar⟩ := exists_far d hc.1
    have hxc : x ≠ c := by
      intro h
      subst x
      rw [metric_self hd] at hfar
      linarith
    have hxp : x ≠ p := by intro h; exact hp (h ▸ hx)
    let A := (C.erase x) ∪ {p}
    let B : Cluster n := {x}
    have hcA : c ∈ A := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Ne.symm hxc, hc.1⟩)
    have hpA : p ∈ A := Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro y hyA hyB
      have hyx : y = x := Finset.mem_singleton.mp hyB
      subst y
      rcases Finset.mem_union.mp hyA with h | h
      · exact (Finset.mem_erase.mp h).1 rfl
      · exact hxp (Finset.mem_singleton.mp h)
    have hcover : A ∪ B = C ∪ D := by
      ext y
      simp only [A, B, hDsingle, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
      by_cases hyx : y = x
      · subst y; simp [hx]
      · simp [hyx]
    have hAnO : A ∉ O := mixed_block_not_mem hO.1 hC hD hCD hcA hc.1 hpA hpD
    have hrA : radius e A ≤ γ * radius d C := by
      apply radius_le e hcA
      intro y hy
      rcases Finset.mem_union.mp hy with hyC | hyp
      · exact (hebound c y).2.trans (mul_le_mul_of_nonneg_left (dist_le_radius hc (Finset.mem_erase.mp hyC).2) hγ0)
      · have hyp' : y = p := Finset.mem_singleton.mp hyp
        subst y
        rw [hec p hpD]
        exact hcp
    have hrB : radius e B = 0 := by rw [radius_singleton, hediag]
    have hrD : radius d D = 0 := by rw [hDsingle, radius_singleton, metric_self hd]
    apply hbad A B ⟨c, hcA⟩ (Finset.singleton_nonempty x) hAB hcover hAnO
    rw [hrB, hrD]
    linarith
  · obtain ⟨q, hq⟩ := exists_optimal_center d hDn
    by_cases hqp : q ≠ p
    · let A := C ∪ {p}
      let B := D.erase p
      have hcA : c ∈ A := Finset.mem_union_left _ hc.1
      have hpA : p ∈ A := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hqB : q ∈ B := Finset.mem_erase.mpr ⟨hqp, hq.1⟩
      have hAB : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro y hyA hyB
        obtain ⟨hyp, hyD⟩ := Finset.mem_erase.mp hyB
        rcases Finset.mem_union.mp hyA with hyC | hyp'
        · exact Finset.disjoint_left.mp hCDdis hyC hyD
        · exact hyp (Finset.mem_singleton.mp hyp')
      have hcover : A ∪ B = C ∪ D := by
        ext y
        simp only [A, B, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
        by_cases hyp : y = p
        · subst y; simp [hpD]
        · simp [hyp]
      have hAnO : A ∉ O := mixed_block_not_mem hO.1 hC hD hCD hcA hc.1 hpA hpD
      have hrA : radius e A ≤ γ * radius d C := by
        apply radius_le e hcA
        intro y hy
        rcases Finset.mem_union.mp hy with hyC | hyp
        · exact (hebound c y).2.trans (mul_le_mul_of_nonneg_left (dist_le_radius hc hyC) hγ0)
        · have hyp' : y = p := Finset.mem_singleton.mp hyp
          subst y
          rw [hec p hpD]
          exact hcp
      have hrB : radius e B ≤ γ * radius d D := by
        apply radius_le e hqB
        intro y hy
        exact (hebound q y).2.trans (mul_le_mul_of_nonneg_left (dist_le_radius hq (Finset.mem_erase.mp hy).2) hγ0)
      apply hbad A B ⟨c, hcA⟩ ⟨q, hqB⟩ hAB hcover hAnO
      linarith
    · have hqp' : q = p := not_ne_iff.mp hqp
      subst q
      have hrest : (D.erase p).Nonempty := by
        by_contra hnrest
        apply hDsingle
        ext y
        simp only [Finset.mem_singleton]
        constructor
        · intro hy
          by_contra hyp
          exact hnrest ⟨y, Finset.mem_erase.mpr ⟨hyp, hy⟩⟩
        · intro hyp
          subst y
          exact hpD
      obtain ⟨y, hyrest⟩ := hrest
      let A := C ∪ (D.erase p)
      let B : Cluster n := {p}
      have hcA : c ∈ A := Finset.mem_union_left _ hc.1
      have hyA : y ∈ A := Finset.mem_union_right _ hyrest
      have hAB : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro z hzA hzB
        have hzp : z = p := Finset.mem_singleton.mp hzB
        subst z
        rcases Finset.mem_union.mp hzA with hpC | hpRest
        · exact hp hpC
        · exact (Finset.mem_erase.mp hpRest).1 rfl
      have hcover : A ∪ B = C ∪ D := by
        ext z
        simp only [A, B, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
        by_cases hzp : z = p
        · subst z; simp [hpD]
        · simp [hzp]
      have hAnO : A ∉ O := mixed_block_not_mem hO.1 hC hD hCD hcA hc.1 hyA (Finset.mem_erase.mp hyrest).2
      have hrD0 : 0 ≤ radius d D := radius_nonneg hd hDn
      have hrA : radius e A ≤ γ * radius d C + radius d D := by
        apply radius_le e hcA
        intro z hz
        rcases Finset.mem_union.mp hz with hzC | hzD
        · have h := (hebound c z).2.trans (mul_le_mul_of_nonneg_left (dist_le_radius hc hzC) hγ0)
          linarith
        · have hzD' := (Finset.mem_erase.mp hzD).2
          rw [hec z hzD']
          have htri := metric_triangle hd c p z
          have hpz := dist_le_radius hq hzD'
          linarith
      have hrB : radius e B = 0 := by rw [radius_singleton, hediag]
      apply hbad A B ⟨c, hcA⟩ (Finset.singleton_nonempty p) hAB hcover hAnO
      rw [hrB]
      nlinarith

end CenterAux

namespace CenterAux

lemma setDistance_attained {n : ℕ} (d : Point n → Point n → ℝ)
    {D E : Cluster n} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∃ x ∈ D, ∃ y ∈ E, setDistance d D E = (d x y : EReal) := by
  classical
  have hp : (D ×ˢ E).Nonempty := hD.product hE
  obtain ⟨p, hpDE, hmin⟩ := Finset.exists_mem_eq_inf' hp (fun p => d p.1 p.2)
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpDE
  refine ⟨p.1, hx, p.2, hy, ?_⟩
  apply le_antisymm
  · exact sInf_le ⟨p.1, hx, p.2, hy, rfl⟩
  · apply le_sInf
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    apply EReal.coe_le_coe_iff.mpr
    have hab : (a, b) ∈ D ×ˢ E := Finset.mem_product.mpr ⟨ha, hb⟩
    have h := Finset.inf'_le (fun p : Point n × Point n => d p.1 p.2) hab
    rw [hmin] at h
    exact h

lemma separation_consequences {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (γ : ℝ) (hγ : 1 < γ)
    (C : Cluster n) (hC : C.Nonempty) (c : Point n) (hc : OptimalCenter d C c)
    (hsep : ∀ p : Point n, p ∉ C → γ * radius d C < d c p) :
    ((γ - 1) * radius d C : EReal) < setDistance d C (Finset.univ \ C) ∧
      C = ball d c (radius d C) ∧ C = ball d c (γ * radius d C) := by
  classical
  have hr : 0 ≤ radius d C := radius_nonneg hd hC
  have hscale : radius d C ≤ γ * radius d C := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · by_cases hcomp : (Finset.univ \ C).Nonempty
    · obtain ⟨x, hx, y, hy, hdist⟩ := setDistance_attained d hC hcomp
      have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
      have hlow := hsep y hyC
      have hcx := dist_le_radius hc hx
      have htri := metric_triangle hd c x y
      have hreal : (γ - 1) * radius d C < d x y := by nlinarith
      rw [hdist]
      simpa only [EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using
        (EReal.coe_lt_coe_iff.mpr hreal)
    · have hempty : Finset.univ \ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcomp
      rw [hempty]
      have hdist : setDistance d C ∅ = ⊤ := by simp [setDistance]
      rw [hdist]
      have htop : (((γ - 1) * radius d C : ℝ) : EReal) < ⊤ := EReal.coe_lt_top _
      simpa only [EReal.coe_mul, EReal.coe_sub, EReal.coe_one] using htop
  · ext x
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hx => dist_le_radius hc hx
    · intro hx
      by_contra hn
      have h := hsep x hn
      linarith
  · ext x
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hx => (dist_le_radius hc hx).trans hscale
    · intro hx
      by_contra hn
      exact not_lt_of_ge hx (hsep x hn)

end CenterAux

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ)
    (O : Partition n) (hO : Stable d k γ O)
    (C : Cluster n) (hC : C ∈ O) (c : Point n) (hc : OptimalCenter d C c) :
    (∀ p : Point n, p ∉ C → γ * radius d C < d c p) ∧
    ((γ - 1) * radius d C : EReal) < setDistance d C (Finset.univ \ C) ∧
    C = ball d c (radius d C) ∧ C = ball d c (γ * radius d C)  := by
  have hsep := CenterAux.point_separation d hd k γ hγ O hO C hC c hc
  exact ⟨hsep, CenterAux.separation_consequences d hd γ hγ C (hO.1.2.1 C hC) c hc hsep⟩
