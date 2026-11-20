-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.hub_inflation_costs
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T16:08:42.54118+00:00
-- url     : https://prove2.me/submissions/101150d0-a65c-40c1-aa8c-a4ef0272dc35

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Supplement

private theorem attained_optimum {n k : ℕ} (d : Point n → Point n → ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ A, Feasible Finset.univ k A ∧ cost d A = optimumValue d k := by
  let label (x : Fin n) : Fin k := ⟨min x.val (k-1), by omega⟩
  let fiber (i : Fin k) := Finset.univ.filter (fun x : Fin n => label x = i)
  have mem_fiber (x : Fin n) (i : Fin k) : x ∈ fiber i ↔ label x = i := by simp [fiber]
  have hits (i : Fin k) : (fiber i).Nonempty := by
    refine ⟨⟨i.val, by omega⟩, (mem_fiber _ _).2 (Fin.ext ?_)⟩
    change min i.val (k-1) = i.val
    omega
  have inj : Function.Injective fiber := by
    intro i j eq
    obtain ⟨x,hx⟩ := hits i
    exact ((mem_fiber _ _).1 hx).symm.trans ((mem_fiber _ _).1 (eq ▸ hx))
  let A := Finset.univ.image fiber
  have hA : Feasible Finset.univ k A := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [A, Finset.card_image_of_injective _ inj]
    · intro C hC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact hits i
    · intro B hB C hC hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact hne (congrArg fiber (((mem_fiber _ _).1 hxi).symm.trans ((mem_fiber _ _).1 hxj)))
    · apply Finset.eq_univ_of_forall
      intro x
      exact Finset.mem_biUnion.mpr ⟨fiber (label x), Finset.mem_image_of_mem _ (Finset.mem_univ _),
        (mem_fiber _ _).2 rfl⟩
  let F := (Finset.univ : Finset (Partition n)).filter (Feasible Finset.univ k)
  have hF : F.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA⟩⟩
  obtain ⟨B,hB,hcost⟩ := Finset.exists_mem_eq_inf' hF (cost d)
  exact ⟨B,(Finset.mem_filter.mp hB).2, by simpa [optimumValue, F, hF] using hcost.symm⟩

private theorem map_feasible {n m j : ℕ} (e : Point n ↪ Point m) {A : Partition n}
    (h : Feasible Finset.univ j A) :
    Feasible (Finset.univ.map e) j (A.image (Finset.map e)) := by
  refine ⟨(Finset.card_image_of_injective _ (Finset.map_injective e)).trans h.1, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hC
    exact (h.2.1 B hB).map
  · intro B hB C hC hne
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hC
    exact (Finset.disjoint_map e).2 (h.2.2.1 hU hV (fun eq => hne (congrArg _ eq)))
  · ext x
    constructor
    · intro hx
      obtain ⟨_,hB,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨y,Finset.mem_univ _,rfl⟩
    · intro hx
      obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
      have hy : y ∈ A.biUnion id := h.2.2.2 ▸ Finset.mem_univ _
      obtain ⟨B,hB,hy⟩ := Finset.mem_biUnion.mp hy
      exact Finset.mem_biUnion.mpr ⟨B.map e,Finset.mem_image_of_mem _ hB,Finset.mem_map.mpr ⟨_,hy,rfl⟩⟩

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

private theorem map_cost {n m : ℕ} (e : Point n ↪ Point m)
    (d : Point n → Point n → ℝ) (p : Point m → Point m → ℝ)
    (he : ∀ x y, p (e x) (e y) = d x y) (A : Partition n) :
    cost p (A.image (Finset.map e)) = cost d A := by
  unfold cost
  rw [Finset.sum_image (Finset.map_injective e).injOn]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : C.Nonempty
  · rw [radius, dif_pos hC.map, radius, dif_pos hC, Finset.inf'_map]
    apply Finset.inf'_congr _ rfl
    intro c _
    change eccentricity p (C.map e) (e c) = eccentricity d C c
    rw [eccentricity, dif_pos hC.map, eccentricity, dif_pos hC, Finset.sup'_map]
    exact Finset.sup'_congr _ rfl (fun x _ => he c x)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hC, radius]

private theorem constant_radius {n : ℕ} (p : Point n → Point n → ℝ) {C : Cluster n}
    (hne : C.Nonempty) (s : ℝ) (upper : ∀ c ∈ C, ∀ x ∈ C, p c x ≤ s)
    (attains : ∀ c ∈ C, ∃ x ∈ C, p c x = s) : radius p C = s := by
  rw [radius,dif_pos hne]
  refine Finset.inf'_eq_of_forall _ _ (fun c hc => ?_)
  rw [eccentricity,dif_pos hne]
  obtain ⟨x,hx,heq⟩ := attains c hc
  exact le_antisymm (Finset.sup'_le _ _ (upper c hc)) (heq ▸ Finset.le_sup' (p c) hx)

theorem solution {n k : ℕ} (d : Point n → Point n → ℝ) (γ τ s : ℝ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray d)
    (hD : diameter d Finset.univ ≤ hubRadius d γ τ)
    (hs : hubRadius d γ τ ≤ s) (hδ : 0 ≤ dummyDistance d γ τ) :
    let dp := hubDistance d k γ τ
    let p := fun (x y : Point (n + k + 2)) =>
      if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n) then s else dp x y
    cost p (suppliedPartition n k) = s ∧
      ∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ suppliedPartition n k ∧
        cost p Q = dummyDistance d γ τ + optimumValue d k := by
  let N := n + k + 2
  let u : Point N := ⟨n, by dsimp [N]; omega⟩
  let e : Point n ↪ Point N := ⟨fun x => ⟨x.val, by dsimp [N]; omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun z : Point N => z.val) h)⟩
  let x₀ : Point n := ⟨0, by omega⟩
  let p (x y : Point N) := if (x.val = n ∧ y.val < n) ∨ (y.val = n ∧ x.val < n)
    then s else hubDistance d k γ τ x y
  let X := hubSource n k
  let Z := (Finset.univ : Cluster N).filter (fun x => n < x.val)
  let U : Cluster N := {u}
  let D := dummyDistance d γ τ
  change cost p (suppliedPartition n k) = s ∧ ∃ Q, Feasible Finset.univ (k+2) Q ∧
    Q ≠ suppliedPartition n k ∧ cost p Q = D + optimumValue d k
  have memX (x : Point N) : x ∈ X ↔ x.val ≤ n := by simp [X,hubSource]
  have memZ (x : Point N) : x ∈ Z ↔ n < x.val := by simp [Z]
  have huX : u ∈ X := (memX _).2 le_rfl
  have src_lt (x : Point n) : (e x).val < n := x.isLt
  have src_in_X : e x₀ ∈ X := (memX _).2 (src_lt _).le
  have hx₀u : e x₀ ≠ u := by
    intro eq
    have heq := congrArg Fin.val eq
    have := src_lt x₀
    change (e x₀).val = n at heq
    omega
  obtain ⟨m,hdist⟩ := hd
  let _ : MetricSpace (Point n) := m
  have dself (x : Point n) : d x x = 0 := by rw [← hdist]; exact dist_self _
  have pself (x : Point N) : p x x = 0 := by
    have h : ¬ ((x.val = n ∧ x.val < n) ∨ (x.val = n ∧ x.val < n)) := by omega
    simp only [p,if_neg h,hubDistance,if_true]
  have psrc (x y : Point n) : p (e x) (e y) = d x y := by
    by_cases heq : x = y
    · subst y
      rw [pself,dself]
    · have hne : e x ≠ e y := fun h => heq (e.injective h)
      have hx := src_lt x
      have hy := src_lt y
      simp only [p,ne_of_lt hx,ne_of_lt hy,false_and,or_self,if_false,hubDistance,if_neg hne,dif_pos hx,dif_pos hy]
      rfl
  have dBound (x y : Point n) : d x y ≤ diameter d Finset.univ := by
    have hne : (Finset.univ : Cluster n).Nonempty := ⟨x,Finset.mem_univ _⟩
    rw [diameter,dif_pos hne]
    refine le_trans ?_ (Finset.le_sup' (eccentricity d _) (Finset.mem_univ x))
    rw [eccentricity,dif_pos hne]
    exact Finset.le_sup' (d x) (Finset.mem_univ y)
  have s0 : 0 ≤ s := (dself x₀ ▸ dBound x₀ x₀).trans (hD.trans hs)
  have p_hub_src (y : Point N) (hy : y.val < n) :
      p u y = s ∧ p y u = s :=
    ⟨if_pos (Or.inl ⟨rfl,hy⟩),if_pos (Or.inr ⟨rfl,hy⟩)⟩
  have classify (x : Point N) (hx : x ∈ X) : x = u ∨ ∃ a, e a = x := by
    by_cases h : x.val = n
    · exact Or.inl (Fin.ext h)
    · exact Or.inr ⟨⟨x.val,lt_of_le_of_ne ((memX _).1 hx) h⟩,Fin.ext rfl⟩
  have radX : radius p X = s := by
    apply constant_radius _ ⟨u,huX⟩
    · intro c hc x hx
      rcases classify c hc with rfl | ⟨a,rfl⟩ <;> rcases classify x hx with rfl | ⟨b,rfl⟩
      · simpa only [pself] using s0
      · exact ((p_hub_src _ (src_lt _)).1).le
      · exact ((p_hub_src _ (src_lt _)).2).le
      · rw [psrc]
        exact (dBound a b).trans (hD.trans hs)
    · intro c hc
      rcases classify c hc with rfl | ⟨a,rfl⟩
      · exact ⟨e x₀,src_in_X,(p_hub_src _ (src_lt _)).1⟩
      · exact ⟨u,huX,(p_hub_src _ (src_lt _)).2⟩
  have single (x : Point N) : radius p {x} = 0 := by simp [radius,eccentricity,pself]
  let singles := Z.image (fun x => ({x} : Cluster N))
  have Xout : X ∉ singles := by
    intro h
    obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp h
    have he : u = z := Finset.mem_singleton.mp (heq.symm ▸ huX)
    have hz' := (memZ _).1 hz
    subst z
    exact (lt_irrefl n) hz'
  constructor
  · change (∑ C ∈ insert X singles, radius p C) = s
    rw [Finset.sum_insert Xout,radX]
    have hz : ∑ C ∈ singles, radius p C = 0 := by
      apply Finset.sum_eq_zero
      intro C hC
      obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hC
      exact single z
    rw [hz,add_zero]
  obtain ⟨A,hA,hopt⟩ := attained_optimum d hk hkn
  let B := A.image (Finset.map e)
  let Y := Finset.univ.map e
  have memY (x : Point N) : x ∈ Y ↔ x.val < n := by
    constructor
    · intro hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hx
      exact src_lt _
    · intro hx
      exact Finset.mem_map.mpr ⟨⟨x.val,hx⟩,Finset.mem_univ _,Fin.ext rfl⟩
  have hUY : Disjoint U Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have heq := Finset.mem_singleton.mp hx
    subst x
    exact (lt_irrefl n) ((memY _).1 hy)
  obtain ⟨houtU,hBU⟩ := add_block (map_feasible e hA) (Finset.singleton_nonempty u) hUY
  let z₁ : Point N := ⟨n+1, by dsimp [N]; omega⟩
  let z₂ : Point N := ⟨n+2, by dsimp [N]; omega⟩
  have hz₁ : z₁ ∈ Z := (memZ _).2 (by dsimp [z₁]; omega)
  have hz₂ : z₂ ∈ Z := (memZ _).2 (by dsimp [z₂]; omega)
  have h12 : z₁ ≠ z₂ := by
    intro h
    have hval := congrArg Fin.val h
    change n+1 = n+2 at hval
    omega
  have pZ (x y : Point N) (hx : x ∈ Z) (hy : y ∈ Z) (hne : x ≠ y) : p x y = D := by
    have hx' := (memZ _).1 hx
    have hy' := (memZ _).1 hy
    simp [p,hubDistance,hne,not_lt.mpr hx'.le,not_lt.mpr hy'.le,
      ne_of_gt hx',ne_of_gt hy',D]
  have radZ : radius p Z = D := by
    apply constant_radius _ ⟨_,hz₁⟩
    · intro c hc x hx
      by_cases eq : c = x
      · subst x
        rw [pself]
        exact hδ
      · exact (pZ c x hc hx eq).le
    · intro c hc
      by_cases eq : c = z₁
      · subst c
        exact ⟨_,hz₂,pZ _ _ hc hz₂ h12⟩
      · exact ⟨_,hz₁,pZ _ _ hc hz₁ eq⟩
  have hZU : Disjoint Z (U ∪ Y) := by
    refine Finset.disjoint_left.mpr (fun {x} hx hxy => ?_)
    have hz := (memZ _).1 hx
    rcases Finset.mem_union.mp hxy with hU | hY
    · have eq := Finset.mem_singleton.mp hU
      subst x
      exact (lt_irrefl n) hz
    · exact (not_lt_of_ge hz.le) ((memY _).1 hY)
  obtain ⟨houtZ,hQ⟩ := add_block hBU ⟨_,hz₁⟩ hZU
  have cover : Z ∪ (U ∪ Y) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rcases lt_trichotomy x.val n with h | h | h
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ ((memY _).2 h))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr (Fin.ext h)))
    · exact Finset.mem_union_left _ ((memZ _).2 h)
  refine ⟨insert Z (insert U B),cover ▸ hQ,?_,?_⟩
  · intro eq
    have hmem : U ∈ suppliedPartition n k := eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · have hx : e x₀ ∈ U := heq.symm ▸ src_in_X
      exact hx₀u (Finset.mem_singleton.mp hx)
    · obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hmem
      have he : z = u := Finset.singleton_injective heq
      subst z
      exact (lt_irrefl n) ((memZ _).1 hz)
  · change (∑ C ∈ insert Z (insert U B), radius p C) = _
    rw [Finset.sum_insert houtZ,Finset.sum_insert houtU,radZ,single,zero_add]
    rw [← hopt,← map_cost e d p psrc A]
    rfl
