-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.hub_runner_up
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T16:13:24.257178+00:00
-- url     : https://prove2.me/submissions/680dfa15-1da8-466d-acdb-5a447b44fe07

import Theorems.Thm_StableMSR_Recovery_Supplement_hub_inflation_costs
import Theorems.Thm_StableMSR_Recovery_Supplement_pure_competitor_lower_bound

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Supplement

private theorem add_block {n j : ℕ} {W C : Cluster n} {A : Partition n}
    (h : Feasible W j A) (hne : C.Nonempty) (hd : Disjoint C W) :
    C ∉ A ∧ Feasible (C ∪ W) (j+1) (insert C A) := by
  have hdB {B} (hB : B ∈ A) : Disjoint C B := by
    refine Finset.disjoint_left.mpr (fun {_} hx hy => Finset.disjoint_left.mp hd hx ?_)
    rw [← h.2.2.2]
    exact Finset.mem_biUnion.mpr ⟨B,hB,hy⟩
  have hout : C ∉ A := by
    intro hC
    obtain ⟨x,hx⟩ := hne
    exact Finset.disjoint_left.mp (hdB hC) hx hx
  refine ⟨hout, by simp [hout,h.1], ?_, ?_, by simp [h.2.2.2]⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hne
    · exact h.2.1 B hB
  · intro B hB D hD hBD
    by_cases hBC : B = C
    · subst B
      exact hdB ((Finset.mem_insert.mp hD).resolve_left (Ne.symm hBD))
    · have hBA := (Finset.mem_insert.mp hB).resolve_left hBC
      rcases Finset.mem_insert.mp hD with hDC | hDA
      · subst D
        exact (hdB hBA).symm
      · exact h.2.2.1 hBA hDA hBD

private theorem singleton_partition {n : ℕ} (T : Cluster n) :
    Feasible T T.card (T.image (fun x => ({x} : Cluster n))) := by
  refine ⟨Finset.card_image_of_injective _ Finset.singleton_injective, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.singleton_nonempty _
  · intro B hB C hC hne
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.disjoint_singleton.mpr (fun h => hne (congrArg _ h))
  · ext x
    simp

private theorem source_bounds {n k : ℕ} (d : Point n → Point n → ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d) :
    0 ≤ optimumValue d k ∧ optimumValue d k ≤ diameter d Finset.univ ∧
    ∀ x y, d x y ≤ diameter d Finset.univ := by
  obtain ⟨m,hm⟩ := hd
  let _ : MetricSpace (Point n) := m
  have diag (x : Point n) : d x x = 0 := by rw [← hm]; exact dist_self _
  have bound (x y : Point n) : d x y ≤ diameter d Finset.univ := by
    have hn : (Finset.univ : Cluster n).Nonempty := ⟨x,Finset.mem_univ _⟩
    rw [diameter,dif_pos hn]
    refine le_trans ?_ (Finset.le_sup' (eccentricity d _) (Finset.mem_univ x))
    rw [eccentricity,dif_pos hn]
    exact Finset.le_sup' (d x) (Finset.mem_univ y)
  obtain ⟨T,_,hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Cluster n)) (n := k-1) (by simp; omega)
  have hC : Tᶜ.Nonempty := Finset.card_pos.mp (by rw [Finset.card_compl,hT]; simp; omega)
  let A := insert Tᶜ (T.image (fun x => ({x} : Cluster n)))
  obtain ⟨hout,hA⟩ := add_block (singleton_partition T) hC disjoint_compl_left
  have hAk : Feasible Finset.univ k A := by
    have hj : T.card+1 = k := by omega
    have cover : Tᶜ ∪ T = Finset.univ := by ext x; simp [em']
    simpa [A,hj,cover] using hA
  let F := (Finset.univ : Finset (Partition n)).filter (Feasible Finset.univ k)
  have hmem : A ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAk⟩
  have hF : F.Nonempty := ⟨A,hmem⟩
  have hv : optimumValue d k = F.inf' hF (cost d) := by simp [optimumValue,F,hF]
  rw [hv]
  refine ⟨Finset.le_inf' _ _ (fun Q _ => ?_),(Finset.inf'_le (cost d) hmem).trans ?_,bound⟩
  · apply Finset.sum_nonneg
    intro C _
    by_cases h : C.Nonempty
    · rw [radius,dif_pos h]
      apply Finset.le_inf'
      intro c hc
      rw [eccentricity,dif_pos h,← diag c]
      exact Finset.le_sup' (d c) hc
    · simp [radius,h]
  · change (∑ C ∈ insert Tᶜ _, radius d C) ≤ _
    rw [Finset.sum_insert hout, Finset.sum_eq_zero (fun B hB => ?_),add_zero]
    · have hn := hC
      obtain ⟨x,hx⟩ := hn
      rw [radius,dif_pos hC]
      refine (Finset.inf'_le _ hx).trans ?_
      rw [eccentricity,dif_pos hC]
      exact Finset.sup'_le _ _ (fun y _ => bound x y)
    · obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hB
      simp [radius,eccentricity,diag]

private theorem supplied_feasible (n k : ℕ) :
    Feasible Finset.univ (k+2) (suppliedPartition n k) := by
  let Z := (Finset.univ : Cluster (n+k+2)).filter (fun x => n < x.val)
  let X := hubSource n k
  have memX (x : Point (n+k+2)) : x ∈ X ↔ x.val ≤ n := by simp [X,hubSource]
  have memZ (x : Point (n+k+2)) : x ∈ Z ↔ n < x.val := by simp [Z]
  let f (i : Fin (k+1)) : Point (n+k+2) := ⟨n+1+i.val,by omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have := congrArg Fin.val h
    apply Fin.ext
    dsimp [f] at this
    omega
  have him : Z = Finset.univ.image f := by
    ext x
    rw [memZ,Finset.mem_image]
    constructor
    · intro h
      refine ⟨⟨x.val-(n+1),by omega⟩,Finset.mem_univ _, Fin.ext ?_⟩
      dsimp [f]
      omega
    · rintro ⟨i,_,rfl⟩
      dsimp [f]
      omega
  have card : Z.card = k+1 := by rw [him,Finset.card_image_of_injective _ hf]; simp
  have hnon : X.Nonempty := ⟨⟨n,by omega⟩,(memX _).2 le_rfl⟩
  have hd : Disjoint X Z := Finset.disjoint_left.mpr (fun {x} hx hz =>
    (not_lt_of_ge ((memX _).1 hx)) ((memZ _).1 hz))
  have cover : X ∪ Z = Finset.univ := by ext x; simp [memX,memZ,le_or_gt]
  have h := (add_block (singleton_partition Z) hnon hd).2
  rw [cover,card] at h
  exact h

set_option maxHeartbeats 1200000 in
private theorem hub_metric {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ)
    (hd : IsMetricArray d) (bd : ∀ x y, d x y ≤ diameter d Finset.univ)
    (hDR : diameter d Finset.univ < hubRadius d γ τ)
    (hR : 0 < hubRadius d γ τ) (hδ : hubRadius d γ τ < dummyDistance d γ τ) :
    IsMetricArray (hubDistance d k γ τ) := by
  obtain ⟨m,hm⟩ := hd
  let _ : MetricSpace (Point n) := m
  have nonneg (x y : Point n) : 0 ≤ d x y := by rw [←hm]; exact dist_nonneg
  have symm (x y : Point n) : d x y = d y x := by rw [←hm,←hm]; exact dist_comm _ _
  have tri (x y z : Point n) : d x z ≤ d x y + d y z := by
    rw [←hm,←hm,←hm]; exact dist_triangle _ _ _
  have sep (x y : Point n) (h : d x y = 0) : x = y := by
    rw [←hm] at h
    exact dist_eq_zero.mp h
  let dp := hubDistance d k γ τ
  have self (x : Point (n+k+2)) : dp x x = 0 := by simp [dp,hubDistance]
  have hc : 0 < crossDistance d γ τ := by unfold crossDistance; linarith
  have hdC : dummyDistance d γ τ < crossDistance d γ τ := by unfold crossDistance; linarith
  have pn (x y) : 0 ≤ dp x y := by
    unfold dp hubDistance
    split_ifs <;> first | exact le_rfl | apply nonneg | linarith
  refine ⟨{dist := dp, dist_self := self, dist_comm := ?_, dist_triangle := ?_, eq_of_dist_eq_zero := ?_}, fun _ _ => rfl⟩
  · intro x y
    by_cases h : x = y
    · subst y; rfl
    unfold dp hubDistance
    rw [if_neg h,if_neg (Ne.symm h)]
    split_ifs <;> first | rfl | apply symm | omega
  · intro x y z
    by_cases hxy : x = y
    · subst y; rw [self,zero_add]
    by_cases hyz : y = z
    · subst z; rw [self,add_zero]
    by_cases hxz : x = z
    · subst z; rw [self]; exact add_nonneg (pn _ _) (pn _ _)
    unfold dp hubDistance
    rw [if_neg hxz,if_neg hxy,if_neg hyz]
    split_ifs <;> first
      | apply tri
      | omega
      | (rename_i h; exact False.elim (hxy (Fin.ext (by omega))))
      | exact False.elim (hyz (Fin.ext (by omega)))
      | exact False.elim (hxz (Fin.ext (by omega)))
      | (apply le_add_of_nonneg_right; first | apply nonneg | linarith)
      | (apply le_add_of_nonneg_left; first | apply nonneg | linarith)
      | (apply le_trans (bd _ _); linarith)
      | linarith
  · intro x y h
    by_contra ne
    unfold dp hubDistance at h
    rw [if_neg ne] at h
    split_ifs at h <;> first
      | exact ne (Fin.ext (congrArg (fun z : Point n => z.val) (sep _ _ h)))
      | linarith

private theorem mixed_cost {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ : ℝ)
    (hd : IsMetricArray (hubDistance d k γ τ)) {Q : Partition (n+k+2)}
    {C : Cluster (n+k+2)} (hC : C ∈ Q) {x z : Point (n+k+2)} (hx : x ∈ C) (hz : z ∈ C)
    (hxX : x.val ≤ n) (hzZ : n < z.val) :
    crossDistance d γ τ ≤ cost (hubDistance d k γ τ) Q := by
  let dp := hubDistance d k γ τ
  obtain ⟨m,hm⟩ := hd
  let _ : MetricSpace (Point (n+k+2)) := m
  have rc0 (B : Cluster (n+k+2)) : 0 ≤ radius dp B := by
    by_cases hb : B.Nonempty
    · rw [radius,dif_pos hb]
      apply Finset.le_inf'
      intro c hc
      rw [eccentricity,dif_pos hb]
      refine le_trans ?_ (Finset.le_sup' (dp c) hc)
      rw [show dp c c = 0 from (hm c c).symm.trans (dist_self c)]
    · simp [radius,hb]
  have cross (v w : Point (n+k+2)) (hv : v.val ≤ n) (hw : n < w.val) :
      dp v w = crossDistance d γ τ := by
    have hne : v ≠ w := fun h => (by subst w; omega)
    unfold dp hubDistance
    rw [if_neg hne]
    split_ifs <;> first | rfl | omega
  have hne : C.Nonempty := ⟨x,hx⟩
  refine le_trans ?_ (Finset.single_le_sum (fun B _ => rc0 B) hC)
  rw [radius,dif_pos hne]
  apply Finset.le_inf'
  intro c hc
  rw [eccentricity,dif_pos hne]
  by_cases h : c.val ≤ n
  · exact (cross c z h hzZ).symm ▸ Finset.le_sup' (dp c) hz
  · have eq : dp c x = crossDistance d γ τ := by
      calc dp c x = dp x c := (hm c x).symm.trans ((dist_comm c x).trans (hm x c))
           _ = _ := cross x c hxX (by omega)
    exact eq ▸ Finset.le_sup' (dp c) hx

theorem solution {n k : ℕ} (d : Point n → Point n → ℚ) (γ τ : ℚ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray (fun x y => (d x y : ℝ)))
    (hγ : 1 < γ) (hτ : 0 < τ) :
    let dr := fun x y => (d x y : ℝ)
    let a := optimumValue dr k
    let dp := hubDistance dr k γ τ
    let O₀ := suppliedPartition n k
    a ≤ diameter dr Finset.univ ∧ diameter dr Finset.univ < hubRadius dr γ τ ∧
    IsMetricArray dp ∧ cost dp O₀ = hubRadius dr γ τ ∧
    (∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ O₀ ∧ cost dp Q = dummyDistance dr γ τ + a) ∧
    (∀ Q, Feasible Finset.univ (k + 2) Q → Q ≠ O₀ → dummyDistance dr γ τ + a ≤ cost dp Q) ∧
    UniqueOptimal dp Finset.univ (k + 2) O₀ := by
  let dr := fun x y => (d x y : ℝ)
  let dp := hubDistance dr k γ τ
  let R := hubRadius dr γ τ
  let δ := dummyDistance dr γ τ
  let a := optimumValue dr k
  let O := suppliedPartition n k
  change a ≤ _ ∧ _ < R ∧ IsMetricArray dp ∧ cost dp O = R ∧
    (∃ Q, Feasible Finset.univ (k+2) Q ∧ Q ≠ O ∧ cost dp Q = δ+a) ∧
    (∀ Q, Feasible Finset.univ (k+2) Q → Q ≠ O → δ+a ≤ cost dp Q) ∧
    UniqueOptimal dp Finset.univ (k+2) O
  obtain ⟨ha0,haD,hbd⟩ := source_bounds dr hk hkn hd
  have hg : 0 < (γ : ℝ)-1 := sub_pos.mpr (by exact_mod_cast hγ)
  have ht : 0 < (τ : ℝ) := by exact_mod_cast hτ
  have hD : 0 ≤ diameter dr Finset.univ := ha0.trans haD
  have hDR : diameter dr Finset.univ < R := by
    dsimp [R,hubRadius]
    linarith [div_pos ht hg]
  have hR := lt_of_le_of_lt hD hDR
  have hgap : R < δ := by
    have hprod : (τ : ℝ) < R * ((γ : ℝ)-1) := by
      calc (τ : ℝ) = ((τ : ℝ) / ((γ : ℝ)-1)) * ((γ : ℝ)-1) := (div_mul_cancel₀ _ hg.ne').symm
           _ < _ := by
             apply mul_lt_mul_of_pos_right _ hg
             change _ < 1 + diameter dr Finset.univ + (τ : ℝ) + _
             linarith
    change R < (γ : ℝ) * R - (τ : ℝ)
    linarith
  have hmetric : IsMetricArray dp := hub_metric dr γ τ hd hbd hDR hR hgap
  have identical (x y : Point (n+k+2)) :
      (if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n) then R else dp x y) = dp x y := by
    split
    · rename_i h
      have hne : x ≠ y := by intro eq; subst y; omega
      unfold dp hubDistance
      rw [if_neg hne]
      split_ifs <;> first | rfl | omega
    · rfl
  have H := hub_inflation_costs dr γ τ R hk hkn hd hDR.le le_rfl (hR.trans hgap).le
  dsimp only at H
  have heq := funext (fun x => funext (identical x))
  rw [heq] at H
  obtain ⟨hc,hatt⟩ := H
  have lower (Q : Partition (n+k+2)) (hQ : Feasible Finset.univ (k+2) Q) (hne : Q ≠ O) :
      δ+a ≤ cost dp Q := by
    by_cases pure : ∀ C ∈ Q, C ⊆ hubSource n k ∨ ∀ x ∈ C, n < x.val
    · exact pure_competitor_lower_bound dr γ τ hk hkn hd hDR hgap Q hQ hne pure
    · push Not at pure
      obtain ⟨C,hC,hnot,z,hz,hzX⟩ := pure
      obtain ⟨x,hx,hxZ⟩ := Finset.not_subset.mp hnot
      have hZ : n < x.val := by simpa [hubSource] using hxZ
      have hcross := mixed_cost dr γ τ hmetric hC hz hx hzX hZ
      refine le_trans ?_ hcross
      change δ + a ≤ δ + R + 1
      linarith [haD.trans hDR.le]
  have hO := supplied_feasible n k
  have strict (Q) (hQ : Feasible Finset.univ (k+2) Q) (hne : Q ≠ O) : cost dp O < cost dp Q := by
    change cost dp O = R at hc
    rw [hc]
    exact lt_of_lt_of_le (lt_of_lt_of_le hgap (le_add_of_nonneg_right ha0)) (lower Q hQ hne)
  refine ⟨haD,hDR,hmetric,hc,hatt,lower,⟨hO,fun Q hQ => ?_⟩,fun Q hQ => ?_⟩
  · by_cases eq : Q = O
    · exact eq ▸ le_rfl
    · exact (strict Q hQ eq).le
  · by_contra ne
    exact (not_lt_of_ge (hQ.2 O hO)) (strict Q hQ.1 ne)
