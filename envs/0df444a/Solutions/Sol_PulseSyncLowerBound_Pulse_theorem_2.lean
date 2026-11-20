-- Prove2me | solution 1 for PulseSyncLowerBound.Pulse.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T03:26:31.302534+00:00
-- url     : https://prove2.me/submissions/aedeff4a-81e1-4b90-82cd-ab54af2b76c3

import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

noncomputable section

namespace PulseSyncLowerBound.Pulse

attribute [local instance 10] Classical.propDecidable Classical.decEq

/-! ### Part 1: Abstract simplicial complexes and combinatorial 0/1-connectivity -/

structure SComplex (V : Type*) where
  mem : Finset V → Prop
  nonempty_of_mem : ∀ {s}, mem s → s.Nonempty
  down_closed : ∀ {s t : Finset V}, mem s → t ⊆ s → t.Nonempty → mem t

namespace SComplex

variable {V : Type*}

def vert (K : SComplex V) (u : V) : Prop := K.mem {u}
def edge (K : SComplex V) (u v : V) : Prop := K.mem {u, v}
def tri (K : SComplex V) (u v w : V) : Prop := K.mem {u, v, w}
def IsNonempty (K : SComplex V) : Prop := ∃ u, K.vert u

lemma vert_of_mem {K : SComplex V} {s : Finset V} (hs : K.mem s) {u : V} (hu : u ∈ s) :
    K.vert u :=
  K.down_closed hs (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty u)

lemma nonempty_iff {K : SComplex V} : K.IsNonempty ↔ ∃ s, K.mem s := by
  constructor
  · rintro ⟨u, hu⟩; exact ⟨{u}, hu⟩
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := K.nonempty_of_mem hs
    exact ⟨u, K.vert_of_mem hs hu⟩

lemma edge_comm {K : SComplex V} {u v : V} : K.edge u v ↔ K.edge v u := by
  simp [edge, Finset.pair_comm]

lemma vert_left_of_edge {K : SComplex V} {u v : V} (h : K.edge u v) : K.vert u :=
  K.vert_of_mem h (by simp)

lemma vert_right_of_edge {K : SComplex V} {u v : V} (h : K.edge u v) : K.vert v :=
  K.vert_of_mem h (by simp)

lemma edge_self_of_vert {K : SComplex V} {u : V} (h : K.vert u) : K.edge u u := by
  simpa [edge, vert] using h

def union (K₁ K₂ : SComplex V) : SComplex V where
  mem s := K₁.mem s ∨ K₂.mem s
  nonempty_of_mem h := h.elim K₁.nonempty_of_mem K₂.nonempty_of_mem
  down_closed h hts ht := h.elim (fun h₁ => Or.inl (K₁.down_closed h₁ hts ht))
    (fun h₂ => Or.inr (K₂.down_closed h₂ hts ht))

def inter (K₁ K₂ : SComplex V) : SComplex V where
  mem s := K₁.mem s ∧ K₂.mem s
  nonempty_of_mem h := K₁.nonempty_of_mem h.1
  down_closed h hts ht := ⟨K₁.down_closed h.1 hts ht, K₂.down_closed h.2 hts ht⟩

def sUnion {ι : Type*} (P : ι → Prop) (F : ι → SComplex V) : SComplex V where
  mem s := ∃ i, P i ∧ (F i).mem s
  nonempty_of_mem := by rintro s ⟨i, _, hs⟩; exact (F i).nonempty_of_mem hs
  down_closed := by rintro s t ⟨i, hi, hs⟩ hts ht; exact ⟨i, hi, (F i).down_closed hs hts ht⟩

def le (K₁ K₂ : SComplex V) : Prop := ∀ ⦃s⦄, K₁.mem s → K₂.mem s

@[ext]
lemma ext {K₁ K₂ : SComplex V} (h : ∀ s, K₁.mem s ↔ K₂.mem s) : K₁ = K₂ := by
  cases K₁; cases K₂; simp only [mk.injEq]; funext s; exact propext (h s)

def mapInj {W : Type*} (K : SComplex V) (f : V → W) : SComplex W where
  mem t := ∃ s, K.mem s ∧ ∀ y, y ∈ t ↔ ∃ x ∈ s, f x = y
  nonempty_of_mem := by
    rintro t ⟨s, hs, hiff⟩
    obtain ⟨x, hx⟩ := K.nonempty_of_mem hs
    exact ⟨f x, (hiff (f x)).mpr ⟨x, hx, rfl⟩⟩
  down_closed := by
    rintro _ t ⟨s, hs, hiff⟩ hts ht
    refine ⟨s.filter (fun x => f x ∈ t), ?_, ?_⟩
    · refine K.down_closed hs (Finset.filter_subset _ _) ?_
      obtain ⟨y, hy⟩ := ht
      obtain ⟨x, hxs, rfl⟩ := (hiff y).mp (hts hy)
      exact ⟨x, Finset.mem_filter.mpr ⟨hxs, hy⟩⟩
    · intro y
      simp only [Finset.mem_filter]
      exact ⟨fun hy => let ⟨x, hxs, hfx⟩ := (hiff y).mp (hts hy); ⟨x, ⟨hxs, hfx ▸ hy⟩, hfx⟩,
             fun ⟨x, ⟨_, hfx_in⟩, hfx⟩ => hfx ▸ hfx_in⟩

def C0 (K : SComplex V) : Prop :=
  K.IsNonempty ∧ ∀ f : V → ℤ, (∀ u v, K.edge u v → f u = f v) →
    ∀ u v, K.vert u → K.vert v → f u = f v

def IsCocycle (K : SComplex V) (ω : V → V → ℤ) : Prop :=
  ∀ u v w, K.tri u v w → ω u v + ω v w = ω u w

def C1 (K : SComplex V) : Prop :=
  K.C0 ∧ ∀ ω : V → V → ℤ, K.IsCocycle ω →
    ∃ ϑ : V → ℤ, ∀ u v, K.edge u v → ω u v = ϑ v - ϑ u

lemma C0_union {K₁ K₂ : SComplex V} (h₁ : K₁.C0) (h₂ : K₂.C0)
    (h₁₂ : (K₁.inter K₂).IsNonempty) : (K₁.union K₂).C0 := by
  obtain ⟨w, hw₁, hw₂⟩ := h₁₂
  refine ⟨⟨w, Or.inl hw₁⟩, fun f hf u v hu hv => ?_⟩
  have hf₁ : ∀ a b, K₁.edge a b → f a = f b := fun a b h => hf a b (Or.inl h)
  have hf₂ : ∀ a b, K₂.edge a b → f a = f b := fun a b h => hf a b (Or.inr h)
  have huw : f u = f w := hu.elim (fun h => h₁.2 f hf₁ u w h hw₁) (fun h => h₂.2 f hf₂ u w h hw₂)
  have hvw : f v = f w := hv.elim (fun h => h₁.2 f hf₁ v w h hw₁) (fun h => h₂.2 f hf₂ v w h hw₂)
  exact huw.trans hvw.symm

lemma C0_star_union {ι : Type*} {A₀ : SComplex V} {P : ι → Prop} {B : ι → SComplex V}
    (hA : A₀.C0) (hB : ∀ i, P i → (B i).C0)
    (hAB : ∀ i, P i → (A₀.inter (B i)).IsNonempty) :
    (A₀.union (sUnion P B)).C0 := by
  obtain ⟨w₀, hw₀⟩ := hA.1
  refine ⟨⟨w₀, Or.inl hw₀⟩, fun f hf u v hu hv => ?_⟩
  have hfA : ∀ a b, A₀.edge a b → f a = f b := fun a b h => hf a b (Or.inl h)
  have val_eq : ∀ x, (A₀.union (sUnion P B)).vert x → f x = f w₀ := by
    rintro x (hxA | ⟨i, hi, hxB⟩)
    · exact hA.2 f hfA x w₀ hxA hw₀
    · obtain ⟨wi, hwiA, hwiB⟩ := hAB i hi
      have hfB : ∀ a b, (B i).edge a b → f a = f b := fun a b h => hf a b (Or.inr ⟨i, hi, h⟩)
      exact ((hB i hi).2 f hfB x wi hxB hwiB).trans (hA.2 f hfA wi w₀ hwiA hw₀)
  exact (val_eq u hu).trans (val_eq v hv).symm

lemma C1_union {K₁ K₂ : SComplex V} (h₁ : K₁.C1) (h₂ : K₂.C1)
    (h₁₂ : (K₁.inter K₂).C0) : (K₁.union K₂).C1 := by
  refine ⟨C0_union h₁.1 h₂.1 h₁₂.1, fun ω hω => ?_⟩
  obtain ⟨ϑ₁, hϑ₁⟩ := h₁.2 ω (fun u v w h => hω u v w (Or.inl h))
  obtain ⟨ϑ₂, hϑ₂⟩ := h₂.2 ω (fun u v w h => hω u v w (Or.inr h))
  obtain ⟨w₀, hw₀⟩ := h₁₂.1
  let c : ℤ := ϑ₁ w₀ - ϑ₂ w₀
  have hdiff : ∀ x, (K₁.inter K₂).vert x → ϑ₁ x - ϑ₂ x = c := by
    intro x hx
    refine h₁₂.2 (fun z => ϑ₁ z - ϑ₂ z) (fun u v huv => ?_) x w₀ hx hw₀
    have e₁ := hϑ₁ u v huv.1
    have e₂ := hϑ₂ u v huv.2
    omega
  refine ⟨fun x => if K₁.vert x then ϑ₁ x else ϑ₂ x + c, fun u v huv => ?_⟩
  dsimp only
  rcases huv with huv₁ | huv₂
  · have hu : K₁.vert u := vert_left_of_edge huv₁
    have hv : K₁.vert v := vert_right_of_edge huv₁
    simp [hu, hv, hϑ₁ u v huv₁]
  · have val₂ : ∀ x, K₂.vert x → (if K₁.vert x then ϑ₁ x else ϑ₂ x + c) = ϑ₂ x + c := by
      intro x hx₂
      split_ifs with hx₁
      · have := hdiff x ⟨hx₁, hx₂⟩
        omega
      · rfl
    rw [val₂ v (vert_right_of_edge huv₂), val₂ u (vert_left_of_edge huv₂)]
    have := hϑ₂ u v huv₂
    omega

lemma mapInj_nonempty {W : Type*} {K : SComplex V} {f : V → W} (h : K.IsNonempty) :
    (K.mapInj f).IsNonempty := by
  obtain ⟨u, hu⟩ := h
  exact ⟨f u, {u}, hu, fun y => by simp [eq_comm]⟩

lemma mapInj_vert_iff {W : Type*} {K : SComplex V} {f : V → W} (_hf : Function.Injective f)
    {y : W} : (K.mapInj f).vert y ↔ ∃ x, K.vert x ∧ f x = y := by
  constructor
  · rintro ⟨s, hs, hiff⟩
    obtain ⟨x, hxs, rfl⟩ := (hiff y).mp (Finset.mem_singleton_self y)
    exact ⟨x, K.vert_of_mem hs hxs, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨{x}, hx, fun z => by simp [eq_comm]⟩

lemma mapInj_edge_iff {W : Type*} {K : SComplex V} {f : V → W} (_hf : Function.Injective f)
    {y₁ y₂ : W} : (K.mapInj f).edge y₁ y₂ ↔ ∃ x₁ x₂, K.edge x₁ x₂ ∧ f x₁ = y₁ ∧ f x₂ = y₂ := by
  constructor
  · rintro ⟨s, hs, hiff⟩
    obtain ⟨x₁, hx₁, rfl⟩ := (hiff y₁).mp (by simp)
    obtain ⟨x₂, hx₂, rfl⟩ := (hiff y₂).mp (by simp)
    refine ⟨x₁, x₂, K.down_closed hs ?_ (by simp), rfl, rfl⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx₁
    · exact Finset.mem_singleton.mp hz ▸ hx₂
  · rintro ⟨x₁, x₂, hx, rfl, rfl⟩
    exact ⟨{x₁, x₂}, hx, fun z => by simp [eq_comm]⟩

lemma mapInj_C0 {W : Type*} {K : SComplex V} {f : V → W} (hf : Function.Injective f)
    (hK : K.C0) : (K.mapInj f).C0 := by
  refine ⟨mapInj_nonempty hK.1, fun g hg y₁ y₂ hy₁ hy₂ => ?_⟩
  obtain ⟨x₁, hx₁, rfl⟩ := (mapInj_vert_iff hf).mp hy₁
  obtain ⟨x₂, hx₂, rfl⟩ := (mapInj_vert_iff hf).mp hy₂
  exact hK.2 (g ∘ f) (fun a b hab => hg (f a) (f b) ((mapInj_edge_iff hf).mpr ⟨a, b, hab, rfl, rfl⟩))
    x₁ x₂ hx₁ hx₂

lemma mapInj_C1 {W : Type*} {K : SComplex V} {f : V → W} (hf : Function.Injective f)
    (hK : K.C1) : (K.mapInj f).C1 := by
  refine ⟨mapInj_C0 hf hK.1, fun ω hω => ?_⟩
  have hω' : K.IsCocycle (fun a b => ω (f a) (f b)) := by
    intro a b c habc
    exact hω (f a) (f b) (f c) ⟨{a, b, c}, habc, fun z => by simp [eq_comm]⟩
  obtain ⟨ϑ', hϑ'⟩ := hK.2 _ hω'
  refine ⟨fun y => if h : ∃ x, f x = y then ϑ' (Classical.choose h) else 0, fun y₁ y₂ hy => ?_⟩
  obtain ⟨x₁, x₂, hx, rfl, rfl⟩ := (mapInj_edge_iff hf).mp hy
  have h₁ : ∃ x, f x = f x₁ := ⟨x₁, rfl⟩
  have h₂ : ∃ x, f x = f x₂ := ⟨x₂, rfl⟩
  have e₁ : Classical.choose h₁ = x₁ := hf (Classical.choose_spec h₁)
  have e₂ : Classical.choose h₂ = x₂ := hf (Classical.choose_spec h₂)
  simp [h₁, h₂, e₁, e₂, hϑ' x₁ x₂ hx]

/-! Gluing along a finite strict total order -/

private lemma exists_max_of_strictOrder {α : Type*} [Fintype α]
    (lt : α → α → Prop)
    (hirrefl : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (htrich : ∀ a b, lt a b ∨ a = b ∨ lt b a)
    (S : Finset α) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, lt x m ∨ x = m := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | @insert a s _ ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, Finset.mem_singleton_self a, fun x hx => Or.inr (Finset.mem_singleton.mp hx)⟩
    · obtain ⟨m, hms, hm⟩ := ih hs
      rcases htrich a m with ham | rfl | hma
      · refine ⟨m, Finset.mem_insert_of_mem hms, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact Or.inl ham
        · exact hm x hxs
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact Or.inr rfl
        · exact hm x hxs
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact Or.inr rfl
        · rcases hm x hxs with hxm | rfl
          · exact Or.inl (htrans x m a hxm hma)
          · exact Or.inl hma

private lemma wf_of_strictOrder {α : Type*} [Fintype α]
    (lt : α → α → Prop)
    (hirrefl : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c) :
    WellFounded lt := by
  refine Subrelation.wf (r := InvImage (· < ·) (fun a : α => (Finset.univ.filter (fun b => lt b a)).card)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  intro x y hxy
  exact Finset.card_lt_card ⟨fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact htrans z x y hz hxy,
    fun hsub => hirrefl x (by
      have hx : x ∈ Finset.univ.filter (fun b => lt b y) := by simp [hxy]
      simpa using hsub hx)⟩

lemma C0_sUnion_of_strictOrder {α : Type*} [Fintype α] [Nonempty α]
    (lt : α → α → Prop)
    (hirrefl : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (htrich : ∀ a b, lt a b ∨ a = b ∨ lt b a)
    (F : α → SComplex V)
    (hF : ∀ a, (F a).C0)
    (hInter : ∀ a, (∃ b, lt b a) → ((sUnion (fun b => lt b a) F).inter (F a)).IsNonempty) :
    (sUnion (fun _ => True) F).C0 := by
  have wf := wf_of_strictOrder lt hirrefl htrans
  have step : ∀ a, (sUnion (fun b => lt b a ∨ b = a) F).C0 := by
    intro a
    induction a using wf.induction with
    | h a ih =>
      by_cases hex : ∃ b, lt b a
      · have hS : (Finset.univ.filter (fun b => lt b a)).Nonempty := by
          obtain ⟨b, hb⟩ := hex; exact ⟨b, by simp [hb]⟩
        obtain ⟨m, hm_mem, hm_max⟩ := exists_max_of_strictOrder lt hirrefl htrans htrich _ hS
        have hma : lt m a := (Finset.mem_filter.mp hm_mem).2
        have eq_lt : sUnion (fun b => lt b a) F = sUnion (fun b => lt b m ∨ b = m) F := by
          ext s; simp only [sUnion]
          refine exists_congr fun b => and_congr_left fun _ => ⟨fun hba => ?_, ?_⟩
          · exact hm_max b (by simp [hba])
          · rintro (hbm | rfl); exact htrans b m a hbm hma; exact hma
        have eq_le : sUnion (fun b => lt b a ∨ b = a) F =
            (sUnion (fun b => lt b a) F).union (F a) := by
          ext s; simp only [sUnion, union]
          constructor
          · rintro ⟨b, hba | rfl, hs⟩
            · exact Or.inl ⟨b, hba, hs⟩
            · exact Or.inr hs
          · rintro (⟨b, hba, hs⟩ | hs)
            · exact ⟨b, Or.inl hba, hs⟩
            · exact ⟨a, Or.inr rfl, hs⟩
        rw [eq_le]
        have hprev : (sUnion (fun b => lt b a) F).C0 := eq_lt ▸ ih m hma
        exact C0_union hprev (hF a) (hInter a hex)
      · have eq_single : sUnion (fun b => lt b a ∨ b = a) F = F a := by
          ext s; simp only [sUnion]
          constructor
          · rintro ⟨b, hba | rfl, hs⟩
            · exact absurd ⟨b, hba⟩ hex
            · exact hs
          · intro hs; exact ⟨a, Or.inr rfl, hs⟩
        rw [eq_single]; exact hF a
  obtain ⟨m, _, hm⟩ := exists_max_of_strictOrder lt hirrefl htrans htrich Finset.univ Finset.univ_nonempty
  have eq_all : sUnion (fun _ => True) F = sUnion (fun b => lt b m ∨ b = m) F := by
    ext s; simp only [sUnion, true_and]
    exact ⟨fun ⟨b, hs⟩ => ⟨b, hm b (Finset.mem_univ b), hs⟩, fun ⟨b, _, hs⟩ => ⟨b, hs⟩⟩
  rw [eq_all]; exact step m

lemma C1_sUnion_of_strictOrder {α : Type*} [Fintype α] [Nonempty α]
    (lt : α → α → Prop)
    (hirrefl : ∀ a, ¬ lt a a)
    (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (htrich : ∀ a b, lt a b ∨ a = b ∨ lt b a)
    (F : α → SComplex V)
    (hF : ∀ a, (F a).C1)
    (hInter : ∀ a, (∃ b, lt b a) → ((sUnion (fun b => lt b a) F).inter (F a)).C0) :
    (sUnion (fun _ => True) F).C1 := by
  have wf := wf_of_strictOrder lt hirrefl htrans
  have step : ∀ a, (sUnion (fun b => lt b a ∨ b = a) F).C1 := by
    intro a
    induction a using wf.induction with
    | h a ih =>
      by_cases hex : ∃ b, lt b a
      · have hS : (Finset.univ.filter (fun b => lt b a)).Nonempty := by
          obtain ⟨b, hb⟩ := hex; exact ⟨b, by simp [hb]⟩
        obtain ⟨m, hm_mem, hm_max⟩ := exists_max_of_strictOrder lt hirrefl htrans htrich _ hS
        have hma : lt m a := (Finset.mem_filter.mp hm_mem).2
        have eq_lt : sUnion (fun b => lt b a) F = sUnion (fun b => lt b m ∨ b = m) F := by
          ext s; simp only [sUnion]
          refine exists_congr fun b => and_congr_left fun _ => ⟨fun hba => ?_, ?_⟩
          · exact hm_max b (by simp [hba])
          · rintro (hbm | rfl); exact htrans b m a hbm hma; exact hma
        have eq_le : sUnion (fun b => lt b a ∨ b = a) F =
            (sUnion (fun b => lt b a) F).union (F a) := by
          ext s; simp only [sUnion, union]
          constructor
          · rintro ⟨b, hba | rfl, hs⟩
            · exact Or.inl ⟨b, hba, hs⟩
            · exact Or.inr hs
          · rintro (⟨b, hba, hs⟩ | hs)
            · exact ⟨b, Or.inl hba, hs⟩
            · exact ⟨a, Or.inr rfl, hs⟩
        rw [eq_le]
        have hprev : (sUnion (fun b => lt b a) F).C1 := eq_lt ▸ ih m hma
        exact C1_union hprev (hF a) (hInter a hex)
      · have eq_single : sUnion (fun b => lt b a ∨ b = a) F = F a := by
          ext s; simp only [sUnion]
          constructor
          · rintro ⟨b, hba | rfl, hs⟩
            · exact absurd ⟨b, hba⟩ hex
            · exact hs
          · intro hs; exact ⟨a, Or.inr rfl, hs⟩
        rw [eq_single]; exact hF a
  obtain ⟨m, _, hm⟩ := exists_max_of_strictOrder lt hirrefl htrans htrich Finset.univ Finset.univ_nonempty
  have eq_all : sUnion (fun _ => True) F = sUnion (fun b => lt b m ∨ b = m) F := by
    ext s; simp only [sUnion, true_and]
    exact ⟨fun ⟨b, hs⟩ => ⟨b, hm b (Finset.mem_univ b), hs⟩, fun ⟨b, _, hs⟩ => ⟨b, hs⟩⟩
  rw [eq_all]; exact step m

end SComplex

/-! ### Part 2: Full-information views, round operators, and Theorem 9 (for k = 1, 2) -/

@[reducible] def View {n : ℕ} (State : Fin n → Type) : ℕ → Fin n → Type
  | 0, i => State i
  | r + 1, i => View State r i × ((j : Fin n) → Option (View State r j))

private lemma opt_map_eq_some {α β : Type*} {o : Option α} {f : α → β} {y : β} :
    o.map f = some y ↔ ∃ x, o = some x ∧ f x = y := by
  cases o <;> simp

instance instFintypeView {n : ℕ} (State : Fin n → Type) [∀ i, Fintype (State i)] :
    (r : ℕ) → (i : Fin n) → Fintype (View State r i)
  | 0, i => by change Fintype (State i); infer_instance
  | r + 1, i => by
      letI : ∀ j, Fintype (View State r j) := instFintypeView State r
      change Fintype (View State r i × ((j : Fin n) → Option (View State r j)))
      infer_instance

abbrev Vert {n : ℕ} (State : Fin n → Type) (r : ℕ) := Σ i : Fin n, View State r i

def initConfig {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) : (i : Fin n) → Option (State i) :=
  fun i => if i ∈ U then some (τ i) else none

def FIRound {n : ℕ} {State : Fin n → Type} {r : ℕ} (k : ℕ)
    (a : (i : Fin n) → Option (View State r i))
    (b : (i : Fin n) → Option (View State (r + 1) i)) : Prop :=
  (Finset.univ.filter (fun i => a i ≠ none ∧ b i = none)).card ≤ k ∧
  ∀ i vm, b i = some vm →
    a i = some vm.1 ∧
    (∀ j, vm.2 j = none ∨ vm.2 j = a j) ∧
    (∀ j, b j ≠ none → vm.2 j = a j)

def FIReach {n : ℕ} {State : Fin n → Type} :
    (r : ℕ) → (Fin r → ℕ) →
    ((i : Fin n) → Option (State i)) →
    ((i : Fin n) → Option (View State r i)) → Prop
  | 0, _, a₀, c => c = a₀
  | r + 1, ks, a₀, c =>
      ∃ b, FIReach r (fun t => ks t.castSucc) a₀ b ∧ FIRound (ks (Fin.last r)) b c

def genComplex {n : ℕ} {State : Fin n → Type} {r : ℕ}
    (P : ((i : Fin n) → Option (View State r i)) → Prop) :
    SComplex (Vert State r) where
  mem s := s.Nonempty ∧ ∃ c, P c ∧ ∀ x ∈ s, c x.1 = some x.2
  nonempty_of_mem h := h.1
  down_closed h hts ht := ⟨ht, let ⟨c, hc, hsc⟩ := h.2; ⟨c, hc, fun x hx => hsc x (hts hx)⟩⟩

def KSingle {n : ℕ} (State : Fin n → Type) (U : Finset (Fin n)) {r : ℕ}
    (ks : Fin r → ℕ) (τ : (i : Fin n) → State i) : SComplex (Vert State r) :=
  genComplex (FIReach r ks (initConfig U τ))

def KAll {n : ℕ} (State : Fin n → Type) (U : Finset (Fin n)) {r : ℕ}
    (ks : Fin r → ℕ) : SComplex (Vert State r) :=
  genComplex (fun c => ∃ τ, FIReach r ks (initConfig U τ) c)

lemma FIReach_mono {n : ℕ} {State : Fin n → Type} {r : ℕ} {ks₁ ks₂ : Fin r → ℕ}
    (hks : ∀ t, ks₁ t ≤ ks₂ t)
    {a₀ : (i : Fin n) → Option (State i)}
    {c : (i : Fin n) → Option (View State r i)}
    (h : FIReach r ks₁ a₀ c) :
    FIReach r ks₂ a₀ c := by
  induction r with
  | zero => exact h
  | succ r ih =>
    obtain ⟨b, hb, hbc⟩ := h
    exact ⟨b, ih (fun t => hks t.castSucc) hb, ⟨hbc.1.trans (hks (Fin.last r)), hbc.2⟩⟩

/-! Crash-free view on a subset `U` -/

def cleanSubView {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) : (r : ℕ) → (i : Fin n) → View State r i
  | 0, i => τ i
  | r + 1, i =>
      (cleanSubView U τ r i,
       fun j => if j ∈ U then some (cleanSubView U τ r j) else none)

def cleanSubCfg {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) (r : ℕ) : (i : Fin n) → Option (View State r i) :=
  fun i => if i ∈ U then some (cleanSubView U τ r i) else none

lemma FIReach_cleanSubCfg {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) (r : ℕ) (ks : Fin r → ℕ) :
    FIReach r ks (initConfig U τ) (cleanSubCfg U τ r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    refine ⟨cleanSubCfg U τ r, ih (fun t => ks t.castSucc), ?_, ?_⟩
    · have hempty : Finset.univ.filter (fun i => cleanSubCfg U τ r i ≠ none ∧ cleanSubCfg U τ (r + 1) i = none) = ∅ := by
        ext i; simp [cleanSubCfg]
      simp [hempty]
    · intro i vm hi
      simp only [cleanSubCfg] at hi
      split_ifs at hi with hiU
      cases hi
      refine ⟨by simp [cleanSubCfg, cleanSubView, hiU], fun j => ?_, fun j hj => ?_⟩
      · by_cases hjU : j ∈ U <;> simp [cleanSubCfg, cleanSubView, hjU]
      · have hjU : j ∈ U := by by_contra h; simp [cleanSubCfg, h] at hj
        simp [cleanSubCfg, cleanSubView, hjU]

lemma KSingle_nonempty {n : ℕ} {State : Fin n → Type} {U : Finset (Fin n)} {r : ℕ}
    (ks : Fin r → ℕ) (τ : (i : Fin n) → State i) (hU : 1 ≤ U.card) :
    (KSingle State U ks τ).IsNonempty := by
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hU
  refine ⟨⟨i₀, cleanSubView U τ r i₀⟩, Finset.singleton_nonempty _,
    cleanSubCfg U τ r, FIReach_cleanSubCfg U τ r ks, ?_⟩
  intro x hx
  rcases Finset.mem_singleton.mp hx with rfl
  simp [cleanSubCfg, hi₀]

lemma single_cfg_C1 {n : ℕ} {State : Fin n → Type} {r : ℕ}
    (c₀ : (i : Fin n) → Option (View State r i))
    (hne : ∃ i₀ v₀, c₀ i₀ = some v₀) :
    (genComplex (fun c => c = c₀)).C1 := by
  obtain ⟨i₀, v₀, hv₀⟩ := hne
  let b : Vert State r := ⟨i₀, v₀⟩
  have hb : (genComplex (fun c => c = c₀)).vert b := by
    refine ⟨Finset.singleton_nonempty _, c₀, (rfl : c₀ = c₀), fun x hx => ?_⟩
    rcases Finset.mem_singleton.mp hx with rfl; exact hv₀
  have hC0 : (genComplex (fun c => c = c₀)).C0 := by
    refine ⟨⟨b, hb⟩, fun f hf u v ⟨_, c₁, hc₁, hu⟩ ⟨_, c₂, hc₂, hv⟩ => ?_⟩
    dsimp only at hc₁ hc₂; subst c₁; subst c₂
    refine hf u v ⟨by simp, c₀, (rfl : c₀ = c₀), fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu x (Finset.mem_singleton_self x)
    · exact hv x (Finset.mem_singleton_self x)
  refine ⟨hC0, fun ω hω => ⟨fun x => ω b x, fun u v ⟨_, c₁, hc₁, huv⟩ => ?_⟩⟩
  dsimp only at hc₁ ⊢; subst c₁
  have htri : (genComplex (fun c => c = c₀)).tri b u v := by
    refine ⟨by simp, c₀, (rfl : c₀ = c₀), fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hv₀
    · exact huv x (by simp)
    · exact huv x (by simp)
  have := hω b u v htri
  omega

/-! `usesProc`, `validFrom`, `mapView`, and `stripView` -/

def usesProc {n : ℕ} {State : Fin n → Type} (p : Fin n) :
    {r : ℕ} → {i : Fin n} → View State r i → Prop
  | 0, i, _ => i = p
  | _ + 1, _, (v, M) => usesProc p v ∨ ∃ j w, M j = some w ∧ usesProc p w

lemma usesProc_self {n : ℕ} {State : Fin n → Type} (p : Fin n) :
    ∀ {r : ℕ} (w : View State r p), usesProc p w
  | 0, _ => rfl
  | _ + 1, (v, _) => Or.inl (usesProc_self p v)

def validFrom {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n)) (τ : (i : Fin n) → State i) :
    {r : ℕ} → {i : Fin n} → View State r i → Prop
  | 0, i, s => i ∈ U ∧ s = τ i
  | _ + 1, _, (v, M) => validFrom U τ v ∧ ∀ j w, M j = some w → validFrom U τ w

lemma validFrom_of_FIReach {n : ℕ} {State : Fin n → Type} {U : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r : ℕ} {ks : Fin r → ℕ}
    {c : (i : Fin n) → Option (View State r i)}
    (h : FIReach r ks (initConfig U τ) c) :
    ∀ i w, c i = some w → validFrom U τ w := by
  induction r with
  | zero =>
    subst h
    intro i s hs
    simp only [initConfig] at hs
    split_ifs at hs with hiU
    exact ⟨hiU, (Option.some.inj hs).symm⟩
  | succ r ih =>
    obtain ⟨b, hb, _, hstep⟩ := h
    intro i vm hvm
    obtain ⟨hbi, hM, _⟩ := hstep i vm hvm
    refine ⟨ih hb i vm.1 hbi, fun j w hjw => ?_⟩
    rcases hM j with hnone | hbj
    · rw [hjw] at hnone; cases hnone
    · exact ih hb j w (hbj.symm.trans hjw)

lemma usesProc_validFrom {n : ℕ} {State : Fin n → Type} {U : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {p : Fin n} :
    ∀ {r : ℕ} {i : Fin n} {w : View State r i},
      validFrom U τ w → usesProc p w → p ∈ U
  | 0, _, _, hv, hp => hp ▸ hv.1
  | _ + 1, _, (_, _), hv, Or.inl hp => usesProc_validFrom hv.1 hp
  | _ + 1, _, (_, _), hv, Or.inr ⟨j, w, hjw, hp⟩ => usesProc_validFrom (hv.2 j w hjw) hp

lemma usesProc_agree {n : ℕ} {State : Fin n → Type} {U₁ U₂ : Finset (Fin n)}
    {τ₁ τ₂ : (i : Fin n) → State i} {p : Fin n} :
    ∀ {r : ℕ} {i : Fin n} {w : View State r i},
      validFrom U₁ τ₁ w → validFrom U₂ τ₂ w → usesProc p w → τ₁ p = τ₂ p
  | 0, _, _, hv₁, hv₂, hp => by subst hp; exact hv₁.2.symm.trans hv₂.2
  | _ + 1, _, (_, _), hv₁, hv₂, Or.inl hp => usesProc_agree hv₁.1 hv₂.1 hp
  | _ + 1, _, (_, _), hv₁, hv₂, Or.inr ⟨j, w, hjw, hp⟩ =>
      usesProc_agree (hv₁.2 j w hjw) (hv₂.2 j w hjw) hp

def mapView {n : ℕ} {State₁ State₂ : Fin n → Type} (f : (i : Fin n) → State₁ i → State₂ i) :
    {r : ℕ} → (i : Fin n) → View State₁ r i → View State₂ r i
  | 0, i, s => f i s
  | _ + 1, i, (v, M) => (mapView f i v, fun j => (M j).map (mapView f j))

lemma mapView_FIReach {n : ℕ} {State₁ State₂ : Fin n → Type}
    (f : (i : Fin n) → State₁ i → State₂ i) {U : Finset (Fin n)}
    {τ : (i : Fin n) → State₁ i} {r : ℕ} {ks : Fin r → ℕ}
    {c : (i : Fin n) → Option (View State₁ r i)}
    (h : FIReach r ks (initConfig U τ) c) :
    FIReach r ks (initConfig U (fun i => f i (τ i))) (fun i => (c i).map (mapView f i)) := by
  induction r with
  | zero =>
    subst h; funext i; dsimp only [View, mapView, initConfig]
    by_cases hi : i ∈ U <;> simp [hi]
  | succ r ih =>
    obtain ⟨b, hb, hcard, hstep⟩ := h
    refine ⟨fun i => (b i).map (mapView f i), ih hb, ?_, ?_⟩
    · convert hcard using 2
      ext i; simp
    · intro i vm' hvm'
      obtain ⟨vm, hci, rfl⟩ := opt_map_eq_some.mp hvm'
      obtain ⟨hbi, hM, hsurv⟩ := hstep i vm hci
      refine ⟨by simp [hbi, mapView], fun j => ?_, fun j hj => ?_⟩
      · rcases hM j with h0 | h1
        · exact Or.inl (by simp [h0, mapView])
        · exact Or.inr (by simp [h1, mapView])
      · have hcj : c j ≠ none := by intro h0; simp [h0] at hj
        simp [hsurv j hcj, mapView]

lemma mapView_id_of_validFrom {n : ℕ} {State : Fin n → Type}
    (f : (i : Fin n) → State i → State i) {U : Finset (Fin n)} {τ : (i : Fin n) → State i} :
    ∀ {r : ℕ} {i : Fin n} {w : View State r i},
      validFrom U τ w → (∀ q, usesProc q w → f q (τ q) = τ q) → mapView f i w = w
  | 0, i, s, hv, hq => by
      have hi : f i (τ i) = τ i := hq i rfl
      rw [mapView, hv.2, hi]
  | _ + 1, i, (v, M), hv, hq => by
      refine Prod.ext (mapView_id_of_validFrom f hv.1 (fun q h => hq q (Or.inl h))) ?_
      funext j
      dsimp only [mapView]
      cases hMj : M j with
      | none => rfl
      | some wj =>
        simp only [Option.map_some, Option.some.injEq]
        exact mapView_id_of_validFrom f (hv.2 j wj hMj)
          (fun q h => hq q (Or.inr ⟨j, wj, hMj, h⟩))

def stripView {n : ℕ} {State : Fin n → Type} (p : Fin n) :
    {r : ℕ} → (i : Fin n) → View State r i → View State r i
  | 0, _, s => s
  | _ + 1, i, (v, M) => (stripView p i v, fun j => if j = p then none else (M j).map (stripView p j))

lemma stripView_eq_of_not_usesProc {n : ℕ} {State : Fin n → Type} (p : Fin n) :
    ∀ {r : ℕ} {i : Fin n} {w : View State r i}, ¬ usesProc p w → stripView p i w = w
  | 0, _, _, _ => rfl
  | _ + 1, i, (v, M), hnot => by
      have hv : ¬ usesProc p v := fun h => hnot (Or.inl h)
      refine Prod.ext (stripView_eq_of_not_usesProc p hv) ?_
      funext j
      dsimp only [stripView]
      by_cases hjp : j = p
      · subst hjp
        simp only [↓reduceIte]
        cases hMp : M j with
        | none => rfl
        | some wp => exact absurd (Or.inr ⟨j, wp, hMp, usesProc_self j wp⟩) hnot
      · simp only [hjp, ↓reduceIte]
        cases hMj : M j with
        | none => rfl
        | some wj =>
          simp only [Option.map_some, Option.some.injEq]
          exact stripView_eq_of_not_usesProc p (fun h => hnot (Or.inr ⟨j, wj, hMj, h⟩))

lemma strip_FIReach {n : ℕ} {State : Fin n → Type} {U : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {p : Fin n} (hpU : p ∈ U) :
    ∀ {r : ℕ} {ks : Fin (r + 1) → ℕ} (hks0 : 1 ≤ ks 0)
      {c : (i : Fin n) → Option (View State (r + 1) i)}
      (h : FIReach (r + 1) ks (initConfig U τ) c)
      (hex : ∃ a wa, c a = some wa ∧ ¬ usesProc p wa),
      c p = none ∧
      FIReach (r + 1) (Fin.cons (ks 0 - 1) (fun t => ks t.succ)) (initConfig (U.erase p) τ)
        (fun i => if i = p then none else (c i).map (stripView p i))
  | 0, ks, hks0, c, ⟨b, hb, hcard, hstep⟩, ⟨a, wa, hca, hnwa⟩ => by
      subst hb
      have hcp : c p = none := by
        by_contra hcp
        obtain ⟨wp, hwp⟩ := Option.ne_none_iff_exists'.mp hcp
        obtain ⟨_, _, hsurv⟩ := hstep a wa hca
        have hMp : wa.2 p = initConfig U τ p := hsurv p hcp
        rw [initConfig, if_pos hpU] at hMp
        exact hnwa (Or.inr ⟨p, τ p, hMp, rfl⟩)
      refine ⟨hcp, initConfig (U.erase p) τ, rfl, ?_, ?_⟩
      · have h0 : Fin.last 0 = (0 : Fin 1) := rfl
        rw [h0] at hcard ⊢
        rw [Fin.cons_zero]
        have hsub : Finset.univ.filter (fun i => initConfig (U.erase p) τ i ≠ none ∧
            (if i = p then none else Option.map (stripView p i) (c i)) = none) =
            (Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ c i = none)).erase p := by
          ext i
          by_cases hip : i = p
          · subst hip; simp [initConfig]
          · simp [initConfig, hip]
        rw [hsub, Finset.card_erase_of_mem]
        · exact Nat.sub_le_sub_right hcard 1
        · simp [initConfig, hpU, hcp]
      · intro i vm' hvm'
        by_cases hip : i = p
        · simp [hip] at hvm'
        · simp only [hip, ↓reduceIte] at hvm'
          obtain ⟨vm, hci, rfl⟩ := opt_map_eq_some.mp hvm'
          obtain ⟨hbi, hM, hsurv⟩ := hstep i vm hci
          have hiU : i ∈ U := by by_contra h; simp [initConfig, h] at hbi
          refine ⟨by simpa [initConfig, Finset.mem_erase, hip, hiU, stripView] using hbi,
            fun j => ?_, fun j hj => ?_⟩
          · by_cases hjp : j = p
            · exact Or.inl (by simp [hjp, stripView])
            · rcases hM j with h0 | h1
              · exact Or.inl (by simp [hjp, h0, stripView])
              · exact Or.inr (by
                  dsimp only [stripView]
                  simp only [hjp, ↓reduceIte]
                  rw [h1]
                  by_cases hjU : j ∈ U <;> simp [initConfig, Finset.mem_erase, hjp, hjU])
          · by_cases hjp : j = p
            · simp [hjp] at hj
            · have hcj : c j ≠ none := by intro h0; simp [hjp, h0] at hj
              have h1 := hsurv j hcj
              have hjU : j ∈ U := by
                obtain ⟨vmj, hcj'⟩ := Option.ne_none_iff_exists'.mp hcj
                have hbj := (hstep j vmj hcj').1
                by_contra h; simp [initConfig, h] at hbj
              simp [hjp, h1, initConfig, hjU, stripView]
  | r + 1, ks, hks0, c, ⟨b, hb, hcard, hstep⟩, ⟨a, wa, hca, hnwa⟩ => by
      obtain ⟨hba, hMa, hsurva⟩ := hstep a wa hca
      have hnva : ¬ usesProc p wa.1 := fun h => hnwa (Or.inl h)
      have ih_res := strip_FIReach hpU (ks := fun t => ks t.castSucc) hks0 hb ⟨a, wa.1, hba, hnva⟩
      have hbp : b p = none := ih_res.1
      have hcp : c p = none := by
        by_contra hcp
        obtain ⟨wp, hwp⟩ := Option.ne_none_iff_exists'.mp hcp
        have := (hstep p wp hwp).1
        rw [hbp] at this; cases this
      refine ⟨hcp, fun i => if i = p then none else (b i).map (stripView p i), ?_, ?_, ?_⟩
      · have eq_cs : (fun t : Fin (r + 1) =>
            (Fin.cons (ks 0 - 1) (fun s : Fin (r + 1) => ks s.succ) : Fin (r + 2) → ℕ) t.castSucc) =
            Fin.cons (ks 0 - 1) (fun t : Fin r => ks t.succ.castSucc) := by
          funext t; cases t using Fin.cases <;> rfl
        rw [eq_cs]; exact ih_res.2
      · have hlast : Fin.last (r + 1) = (Fin.last r).succ := rfl
        rw [hlast, Fin.cons_succ]
        have heq : Finset.univ.filter (fun i =>
            (if i = p then none else Option.map (stripView p i) (b i)) ≠ none ∧
            (if i = p then none else Option.map (stripView p i) (c i)) = none) =
            Finset.univ.filter (fun i => b i ≠ none ∧ c i = none) := by
          ext i
          by_cases hip : i = p
          · subst hip; simp [hbp]
          · simp [hip]
        rw [heq]; exact hcard
      · intro i vm' hvm'
        by_cases hip : i = p
        · simp [hip] at hvm'
        · simp only [hip, ↓reduceIte] at hvm'
          obtain ⟨vm, hci, rfl⟩ := opt_map_eq_some.mp hvm'
          obtain ⟨hbi, hM, hsurv⟩ := hstep i vm hci
          refine ⟨by simp [hip, hbi, stripView], fun j => ?_, fun j hj => ?_⟩
          · by_cases hjp : j = p
            · exact Or.inl (by simp [hjp, stripView])
            · rcases hM j with h0 | h1
              · exact Or.inl (by simp [hjp, h0, stripView])
              · exact Or.inr (by simp [hjp, h1, stripView])
          · by_cases hjp : j = p
            · simp [hjp] at hj
            · have hcj : c j ≠ none := by intro h0; simp [hjp, h0] at hj
              simp [hjp, hsurv j hcj, stripView]

lemma unstrip_FIReach {n : ℕ} {State : Fin n → Type} {U : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {p : Fin n} (hpU : p ∈ U) :
    ∀ {r : ℕ} {k₀' k₀ : ℕ} (_hk : k₀' + 1 ≤ k₀) {ks' : Fin r → ℕ}
      {c : (i : Fin n) → Option (View State (r + 1) i)}
      (_h : FIReach (r + 1) (Fin.cons k₀' ks') (initConfig (U.erase p) τ) c),
      FIReach (r + 1) (Fin.cons k₀ ks') (initConfig U τ) c
  | 0, k₀', k₀, hk, ks', c, ⟨b, hb, hcard, hstep⟩ => by
      subst hb
      refine ⟨initConfig U τ, rfl, ?_, ?_⟩
      · have h0 : Fin.last 0 = (0 : Fin 1) := rfl
        rw [h0] at hcard ⊢
        rw [Fin.cons_zero] at hcard ⊢
        have hsub : Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ c i = none) ⊆
            insert p (Finset.univ.filter (fun i => initConfig (U.erase p) τ i ≠ none ∧ c i = none)) := by
          intro i hi
          by_cases hip : i = p
          · simp [hip]
          · simp [initConfig, hip] at hi ⊢; exact hi
        calc (Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ c i = none)).card
            ≤ (insert p (Finset.univ.filter (fun i => initConfig (U.erase p) τ i ≠ none ∧ c i = none))).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter (fun i => initConfig (U.erase p) τ i ≠ none ∧ c i = none)).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ k₀' + 1 := Nat.add_le_add_right hcard 1
          _ ≤ k₀ := hk
      · intro i vm hci
        obtain ⟨hbi, hM, hsurv⟩ := hstep i vm hci
        have hip : i ≠ p := by intro rfl; simp [initConfig] at hbi
        have hiU : i ∈ U := by by_contra h; simp [initConfig, h] at hbi
        refine ⟨by simpa [initConfig, hip, hiU] using hbi, fun j => ?_, fun j hj => ?_⟩
        · rcases hM j with h0 | h1
          · exact Or.inl h0
          · by_cases hjp : j = p
            · subst hjp; simp [initConfig] at h1; exact Or.inl h1
            · exact Or.inr (by simpa [initConfig, hjp] using h1)
        · have h1 := hsurv j hj
          have hjp : j ≠ p := by
            obtain ⟨vmj, hcj⟩ := Option.ne_none_iff_exists'.mp hj
            have hbj := (hstep j vmj hcj).1
            intro rfl; simp [initConfig] at hbj
          simpa [initConfig, hjp] using h1
  | r + 1, k₀', k₀, hk, ks', c, ⟨b, hb, hcard, hstep⟩ => by
      have eq_cs : (fun t : Fin (r + 1) => (Fin.cons k₀' ks' : Fin (r + 2) → ℕ) t.castSucc) =
          Fin.cons k₀' (fun t : Fin r => ks' t.castSucc) := by
        funext t; cases t using Fin.cases <;> rfl
      have eq_cs2 : (fun t : Fin (r + 1) => (Fin.cons k₀ ks' : Fin (r + 2) → ℕ) t.castSucc) =
          Fin.cons k₀ (fun t : Fin r => ks' t.castSucc) := by
        funext t; cases t using Fin.cases <;> rfl
      rw [eq_cs] at hb
      refine ⟨b, ?_, hcard, hstep⟩
      rw [eq_cs2]
      exact unstrip_FIReach hpU hk hb

/-! Round-1 unfolding via `Round1State` -/

abbrev Round1State {n : ℕ} (State : Fin n → Type) (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) (_ : Fin n) : Type :=
  { M : (j : Fin n) → Option (State j) //
      (∀ j, M j = none ∨ M j = initConfig U τ j) ∧
      (∀ j ∈ W, M j = initConfig U τ j) }

def defaultR1 {n : ℕ} {State : Fin n → Type} (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) (i : Fin n) : Round1State State U W τ i :=
  ⟨initConfig U τ, fun _ => Or.inr rfl, fun _ _ => rfl⟩

instance instNonemptyRound1State {n : ℕ} (State : Fin n → Type)
    (U W : Finset (Fin n)) (τ : (i : Fin n) → State i) (i : Fin n) :
    Nonempty (Round1State State U W τ i) :=
  ⟨defaultR1 U W τ i⟩

def embedView {n : ℕ} {State : Fin n → Type} (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) :
    {r : ℕ} → (i : Fin n) → View (Round1State State U W τ) r i → View State (r + 1) i
  | 0, i, m => (τ i, m.val)
  | _ + 1, i, (v, M) => (embedView U W τ i v, fun j => (M j).map (embedView U W τ j))

private lemma opt_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · cases h
  · cases h
  · exact congrArg some (hf (Option.some.inj h))

lemma embedView_injective {n : ℕ} {State : Fin n → Type} (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) :
    ∀ {r : ℕ} (i : Fin n), Function.Injective (embedView U W τ (r := r) i)
  | 0, _, _, _, h => Subtype.ext (Prod.mk.inj h).2
  | _ + 1, i, (v₁, M₁), (v₂, M₂), h => by
      obtain ⟨hv, hM⟩ := Prod.mk.inj h
      refine Prod.ext (embedView_injective U W τ i hv) ?_
      funext j
      exact opt_map_inj (embedView_injective U W τ j) (congr_fun hM j)

def embedVert {n : ℕ} {State : Fin n → Type} (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) {r : ℕ} (x : Vert (Round1State State U W τ) r) :
    Vert State (r + 1) :=
  ⟨x.1, embedView U W τ x.1 x.2⟩

lemma embedVert_injective {n : ℕ} {State : Fin n → Type} (U W : Finset (Fin n))
    (τ : (i : Fin n) → State i) {r : ℕ} :
    Function.Injective (embedVert U W τ (r := r)) := by
  rintro ⟨i₁, v₁⟩ ⟨i₂, v₂⟩ h
  obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp h
  rw [heq_eq_eq] at hv
  exact Sigma.ext rfl (heq_of_eq (embedView_injective U W τ i₁ hv))

lemma FIReach_succ_iff {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) :
    ∀ {r : ℕ} (ks : Fin (r + 1) → ℕ) (c : (i : Fin n) → Option (View State (r + 1) i)),
      FIReach (r + 1) ks (initConfig U τ) c ↔
      ∃ (W : Finset (Fin n)), W ⊆ U ∧ (U \ W).card ≤ ks 0 ∧
        ∃ (τ₁ : (i : Fin n) → Round1State State U W τ i)
          (c' : (i : Fin n) → Option (View (Round1State State U W τ) r i)),
          FIReach r (fun t => ks t.succ) (initConfig W τ₁) c' ∧
          ∀ i, c i = (c' i).map (embedView U W τ i)
  | 0, ks, c => by
      constructor
      · rintro ⟨b, rfl, hcard, hstep⟩
        let W := Finset.univ.filter (fun i => c i ≠ none)
        have hWU : W ⊆ U := by
          intro i hi
          obtain ⟨vm, hci⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp hi).2
          have hbi := (hstep i vm hci).1
          by_contra hnU; simp [initConfig, hnU] at hbi
        have hU_diff : U \ W = Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ c i = none) := by
          ext i; by_cases hiU : i ∈ U <;> simp [W, initConfig, hiU]
        let τ₁ : (i : Fin n) → Round1State State U W τ i := fun i =>
          if hci : (c i).isSome then
            let vm := (c i).get hci
            have hvm : c i = some vm := (Option.some_get hci).symm
            ⟨vm.2, (hstep i vm hvm).2.1, fun j hjW => (hstep i vm hvm).2.2 j (Finset.mem_filter.mp hjW).2⟩
          else defaultR1 U W τ i
        refine ⟨W, hWU, hU_diff ▸ hcard, τ₁, initConfig W τ₁, rfl, fun i => ?_⟩
        cases hci : c i with
        | none =>
          have hiW : i ∉ W := by simp [W, hci]
          simp [initConfig, hiW]
        | some vm =>
          have hiW : i ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simp [hci]⟩
          have hiU : i ∈ U := hWU hiW
          have h1 : vm.1 = τ i := by
            have hbi := (hstep i vm hci).1
            simpa [initConfig, hiU] using hbi.symm
          have hτ₁ : (τ₁ i).val = vm.2 := by simp [τ₁, hci]
          simp only [initConfig, hiW, ↓reduceIte, Option.map_some, embedView]
          exact congrArg some (Prod.ext h1 hτ₁.symm)
      · rintro ⟨W, hWU, hcard, τ₁, c', rfl, hc⟩
        refine ⟨initConfig U τ, rfl, ?_, ?_⟩
        · have h0 : Fin.last 0 = (0 : Fin 1) := rfl
          rw [h0]
          have hsub : Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ c i = none) = U \ W := by
            ext i; by_cases hiU : i ∈ U <;> by_cases hiW : i ∈ W <;> simp [hc i, initConfig, hiU, hiW]
          rw [hsub]; exact hcard
        · intro i vm hci
          rw [hc i] at hci
          simp only [initConfig] at hci
          split_ifs at hci with hiW
          · simp only [Option.map_some, Option.some.injEq] at hci
            subst hci
            have hiU : i ∈ U := hWU hiW
            refine ⟨by simp [initConfig, hiU, embedView], (τ₁ i).2.1, fun j hj => ?_⟩
            have hjW : j ∈ W := by by_contra h; simp [hc j, initConfig, h] at hj
            exact (τ₁ i).2.2 j hjW
          · simp at hci
  | r + 1, ks, c => by
      constructor
      · rintro ⟨b, hb, hcard, hstep⟩
        obtain ⟨W, hWU, hWcard, τ₁, b', hb', hbeq⟩ :=
          (FIReach_succ_iff U τ (fun t => ks t.castSucc) b).mp hb
        let c' : (i : Fin n) → Option (View (Round1State State U W τ) (r + 1) i) := fun i =>
          if hci : (c i).isSome then
            let vm := (c i).get hci
            have hvm : c i = some vm := (Option.some_get hci).symm
            have hbi : (b' i).map (embedView U W τ i) = some vm.1 := (hbeq i).symm.trans (hstep i vm hvm).1
            let v' := Classical.choose (opt_map_eq_some.mp hbi)
            some (v', fun j => if vm.2 j = none then none else b' j)
          else none
        have hceq : ∀ i, c i = (c' i).map (embedView U W τ i) := by
          intro i
          cases hci : c i with
          | none => simp [c', hci]
          | some vm =>
            have his : (c i).isSome = true := by simp [hci]
            have hget : (c i).get his = vm := by simp [hci]
            have hbi : (b' i).map (embedView U W τ i) = some ((c i).get his).1 :=
              (hbeq i).symm.trans (hstep i _ (Option.some_get his).symm).1
            have hv' : embedView U W τ i (Classical.choose (opt_map_eq_some.mp hbi)) = vm.1 := by
              have hspec := (Classical.choose_spec (opt_map_eq_some.mp hbi)).2
              simpa [hget] using hspec
            have hc'i : c' i = some (Classical.choose (opt_map_eq_some.mp hbi),
                fun j => if vm.2 j = none then none else b' j) := by
              simp only [c', his, ↓reduceDIte]
              congr 1; refine Prod.ext rfl ?_; funext j; simp [hget]
            rw [hc'i, Option.map_some, Option.some.injEq]
            dsimp only [embedView]
            refine Prod.ext hv'.symm ?_
            funext j
            rcases (hstep i vm hci).2.1 j with h0 | h1
            · simp [h0]
            · by_cases hbj : b j = none
              · simp [h1, hbj]
              · have hne : vm.2 j ≠ none := h1 ▸ hbj
                dsimp only
                rw [if_neg hne, ← hbeq j, h1]
        refine ⟨W, hWU, hWcard, τ₁, c', ⟨b', hb', ?_, ?_⟩, hceq⟩
        · have hlast : Fin.last (r + 1) = (Fin.last r).succ := rfl
          rw [hlast] at hcard
          convert hcard using 2
          ext i; simp [hbeq i, hceq i]
        · intro i vm' hc'i
          have hci_some : c i = some (embedView U W τ i vm') := by rw [hceq i, hc'i]; rfl
          obtain ⟨hbi, hM, hsurv⟩ := hstep i _ hci_some
          rw [hbeq i] at hbi
          obtain ⟨v'', hb'i, hv''⟩ := opt_map_eq_some.mp hbi
          have hv_eq : v'' = vm'.1 := embedView_injective U W τ i hv''
          subst hv_eq
          refine ⟨hb'i, fun j => ?_, fun j hj => ?_⟩
          · rcases hM j with h0 | h1
            · dsimp only [embedView] at h0
              cases hmj : vm'.2 j with
              | none => exact Or.inl rfl
              | some _ => rw [hmj] at h0; cases h0
            · dsimp only [embedView] at h1
              rw [hbeq j] at h1
              exact Or.inr (opt_map_inj (embedView_injective U W τ j) h1)
          · have hcj : c j ≠ none := by rw [hceq j]; simpa using hj
            have h1 := hsurv j hcj
            dsimp only [embedView] at h1
            rw [hbeq j] at h1
            exact opt_map_inj (embedView_injective U W τ j) h1
      · rintro ⟨W, hWU, hWcard, τ₁, c', ⟨b', hb', hcard', hstep'⟩, hceq⟩
        have hb : FIReach (r + 1) (fun t => ks t.castSucc) (initConfig U τ)
            (fun i => (b' i).map (embedView U W τ i)) :=
          (FIReach_succ_iff U τ (fun t => ks t.castSucc) _).mpr
            ⟨W, hWU, hWcard, τ₁, b', hb', fun _ => rfl⟩
        refine ⟨fun i => (b' i).map (embedView U W τ i), hb, ?_, ?_⟩
        · have hlast : Fin.last (r + 1) = (Fin.last r).succ := rfl
          rw [hlast]
          convert hcard' using 2
          ext i; simp [hceq i]
        · intro i vm hci
          rw [hceq i] at hci
          obtain ⟨vm', hc'i, rfl⟩ := opt_map_eq_some.mp hci
          obtain ⟨hb'i, hM', hsurv'⟩ := hstep' i vm' hc'i
          refine ⟨by simp [hb'i, embedView], fun j => ?_, fun j hj => ?_⟩
          · rcases hM' j with h0 | h1
            · exact Or.inl (by simp [h0, embedView])
            · exact Or.inr (by simp [h1, embedView])
          · have hc'j : c' j ≠ none := by intro h0; simp [hceq j, h0] at hj
            simp [hsurv' j hc'j, embedView]

lemma KSingle_succ_eq {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) {r : ℕ} (ks : Fin (r + 1) → ℕ) :
    KSingle State U ks τ =
      SComplex.sUnion (fun W : Finset (Fin n) => W ⊆ U ∧ (U \ W).card ≤ ks 0)
        (fun W => (KAll (Round1State State U W τ) W (fun t => ks t.succ)).mapInj (embedVert U W τ)) := by
  ext s
  simp only [KSingle, KAll, genComplex, SComplex.sUnion, SComplex.mapInj]
  constructor
  · rintro ⟨hsne, c, hreach, hsc⟩
    obtain ⟨W, hWU, hWcard, τ₁, c', hreach', hceq⟩ := (FIReach_succ_iff U τ ks c).mp hreach
    let invVert : Vert State (r + 1) → Vert (Round1State State U W τ) r := fun y =>
      if h : ∃ x, c' x.1 = some x.2 ∧ embedVert U W τ x = y then Classical.choose h
      else ⟨y.1, cleanSubView W (defaultR1 U W τ) r y.1⟩
    have hinv : ∀ y ∈ s, c' (invVert y).1 = some (invVert y).2 ∧ embedVert U W τ (invVert y) = y := by
      intro y hy
      have hex : ∃ x : Vert (Round1State State U W τ) r, c' x.1 = some x.2 ∧ embedVert U W τ x = y := by
        have hcy := hsc y hy
        rw [hceq y.1] at hcy
        obtain ⟨v', hc'y, hv'⟩ := opt_map_eq_some.mp hcy
        exact ⟨⟨y.1, v'⟩, hc'y, Sigma.ext rfl (heq_of_eq hv')⟩
      have hinv_eq : invVert y = Classical.choose hex := dif_pos hex
      rw [hinv_eq]
      exact Classical.choose_spec hex
    obtain ⟨y₀, hy₀⟩ := hsne
    refine ⟨W, ⟨hWU, hWcard⟩, s.image invVert,
      ⟨⟨invVert y₀, by simp only [Finset.mem_image]; exact ⟨y₀, hy₀, rfl⟩⟩, c', ⟨τ₁, hreach'⟩, ?_⟩, ?_⟩
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (hinv y hy).1
    · intro y
      simp only [Finset.mem_image]
      exact ⟨fun hy => ⟨invVert y, ⟨y, hy, rfl⟩, (hinv y hy).2⟩,
             fun ⟨_, ⟨z, hz, rfl⟩, hzy⟩ => (hzy.symm.trans (hinv z hz).2) ▸ hz⟩
  · rintro ⟨W, ⟨hWU, hWcard⟩, s', ⟨⟨x₀, hx₀⟩, c', ⟨τ₁, hreach'⟩, hs'c'⟩, hiff⟩
    refine ⟨⟨embedVert U W τ x₀, (hiff _).mpr ⟨x₀, hx₀, rfl⟩⟩,
      fun i => (c' i).map (embedView U W τ i),
      (FIReach_succ_iff U τ ks _).mpr ⟨W, hWU, hWcard, τ₁, c', hreach', fun _ => rfl⟩, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hiff y).mp hy
    simp [embedVert, hs'c' x hx]

/-! Lexicographic order on configurations restricted to `U` -/

abbrev InitCfg {n : ℕ} (State : Fin n → Type) [∀ i, Nonempty (State i)] (U : Finset (Fin n)) : Type :=
  { τ : (i : Fin n) → State i // ∀ i, i ∉ U → τ i = Classical.arbitrary (State i) }

instance instNonemptyInitCfg {n : ℕ} (State : Fin n → Type)
    [∀ i, Nonempty (State i)] (U : Finset (Fin n)) :
    Nonempty (InitCfg State U) :=
  ⟨⟨fun i => Classical.arbitrary (State i), fun _ _ => rfl⟩⟩

def stateRank {n : ℕ} (State : Fin n → Type) [∀ i, Fintype (State i)] (i : Fin n) (s : State i) : ℕ :=
  (Fintype.equivFin (State i) s).val

lemma stateRank_injective {n : ℕ} (State : Fin n → Type) [∀ i, Fintype (State i)] (i : Fin n) :
    Function.Injective (stateRank State i) :=
  fun _ _ h => (Fintype.equivFin (State i)).injective (Fin.ext h)

def cfgLt {n : ℕ} {State : Fin n → Type} [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} (a b : InitCfg State U) : Prop :=
  ∃ p : Fin n, (∀ j, j < p → a.1 j = b.1 j) ∧ stateRank State p (a.1 p) < stateRank State p (b.1 p)

lemma cfgLt_irrefl {n : ℕ} {State : Fin n → Type} [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} (a : InitCfg State U) : ¬ cfgLt a a := by
  rintro ⟨p, _, h⟩; exact Nat.lt_irrefl _ h

lemma cfgLt_trans {n : ℕ} {State : Fin n → Type} [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} (a b c : InitCfg State U) (hab : cfgLt a b) (hbc : cfgLt b c) :
    cfgLt a c := by
  obtain ⟨p₁, heq₁, hlt₁⟩ := hab
  obtain ⟨p₂, heq₂, hlt₂⟩ := hbc
  rcases lt_trichotomy p₁ p₂ with h | rfl | h
  · refine ⟨p₁, fun j hj => (heq₁ j hj).trans (heq₂ j (hj.trans h)), ?_⟩
    rw [← heq₂ p₁ h]; exact hlt₁
  · exact ⟨p₁, fun j hj => (heq₁ j hj).trans (heq₂ j hj), hlt₁.trans hlt₂⟩
  · refine ⟨p₂, fun j hj => (heq₁ j (hj.trans h)).trans (heq₂ j hj), ?_⟩
    rw [heq₁ p₂ h]; exact hlt₂

lemma cfgLt_trich {n : ℕ} {State : Fin n → Type} [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} (a b : InitCfg State U) : cfgLt a b ∨ a = b ∨ cfgLt b a := by
  by_cases hab : a = b
  · exact Or.inr (Or.inl hab)
  · have hdiff : (Finset.univ.filter (fun i : Fin n => a.1 i ≠ b.1 i)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hab; apply Subtype.ext; funext i
      by_contra hne
      have : i ∈ Finset.univ.filter (fun j : Fin n => a.1 j ≠ b.1 j) := by simp [hne]
      rw [h] at this; simp at this
    let S := Finset.univ.filter (fun i : Fin n => a.1 i ≠ b.1 i)
    let p := S.min' hdiff
    have hp_mem : p ∈ S := Finset.min'_mem S hdiff
    have hp_ne : a.1 p ≠ b.1 p := (Finset.mem_filter.mp hp_mem).2
    have hlt_eq : ∀ j, j < p → a.1 j = b.1 j := by
      intro j hj
      by_contra hjne
      have hjS : j ∈ S := by simp [S, hjne]
      exact not_le_of_gt hj (Finset.min'_le S j hjS)
    have hrk_ne : stateRank State p (a.1 p) ≠ stateRank State p (b.1 p) :=
      fun h => hp_ne (stateRank_injective State p h)
    rcases Nat.lt_or_gt_of_ne hrk_ne with hlt | hgt
    · exact Or.inl ⟨p, hlt_eq, hlt⟩
    · exact Or.inr (Or.inr ⟨p, fun j hj => (hlt_eq j hj).symm, hgt⟩)

lemma KAll_eq_sUnion_InitCfg {n : ℕ} (State : Fin n → Type)
    [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    (U : Finset (Fin n)) {r : ℕ} (ks : Fin r → ℕ) :
    KAll State U ks = SComplex.sUnion (fun _ : InitCfg State U => True)
      (fun τ => KSingle State U ks τ.1) := by
  ext s
  simp only [KAll, KSingle, genComplex, SComplex.sUnion, true_and]
  constructor
  · rintro ⟨hsne, c, ⟨τ, hreach⟩, hsc⟩
    let τ' : InitCfg State U := ⟨fun i => if i ∈ U then τ i else Classical.arbitrary (State i),
      fun i hi => by simp [hi]⟩
    have heq : initConfig U τ'.1 = initConfig U τ := by
      funext i; by_cases hi : i ∈ U <;> simp [initConfig, τ', hi]
    exact ⟨τ', hsne, c, heq.symm ▸ hreach, hsc⟩
  · rintro ⟨τ, hsne, c, hreach, hsc⟩
    exact ⟨hsne, c, ⟨τ.1, hreach⟩, hsc⟩

lemma FIReach_silentCrash_cleanSubCfg {n : ℕ} {State : Fin n → Type}
    {U W : Finset (Fin n)} (hWU : W ⊆ U) (τ : (i : Fin n) → State i) :
    ∀ {r' : ℕ} (ks : Fin (r' + 1) → ℕ),
      (U \ W).card ≤ ks 0 →
      FIReach (r' + 1) ks (initConfig U τ) (cleanSubCfg W τ (r' + 1))
  | 0, ks, hcard => by
      refine ⟨initConfig U τ, rfl, ?_, ?_⟩
      · have h0 : Fin.last 0 = (0 : Fin 1) := rfl
        rw [h0]
        have heq : Finset.univ.filter (fun i => initConfig U τ i ≠ none ∧ cleanSubCfg W τ 1 i = none) = U \ W := by
          ext i; by_cases hiU : i ∈ U <;> by_cases hiW : i ∈ W <;> simp [initConfig, cleanSubCfg, hiU, hiW]
        rw [heq]; exact hcard
      · intro i vm hci
        simp only [cleanSubCfg] at hci
        split_ifs at hci with hiW
        cases hci
        have hiU : i ∈ U := hWU hiW
        refine ⟨by simp [initConfig, hiU, cleanSubView], fun j => ?_, fun j hj => ?_⟩
        · by_cases hjW : j ∈ W
          · exact Or.inr (by simp [hjW, initConfig, hWU hjW, cleanSubView])
          · exact Or.inl (by simp [hjW, cleanSubView])
        · have hjW : j ∈ W := by by_contra h; simp [cleanSubCfg, h] at hj
          simp [hjW, initConfig, hWU hjW, cleanSubView]
  | r' + 1, ks, hcard => by
      refine ⟨cleanSubCfg W τ (r' + 1),
        FIReach_silentCrash_cleanSubCfg hWU τ (fun t => ks t.castSucc) hcard, ?_, ?_⟩
      · have hempty : Finset.univ.filter (fun i =>
            cleanSubCfg W τ (r' + 1) i ≠ none ∧ cleanSubCfg W τ (r' + 2) i = none) = ∅ := by
          ext i; simp [cleanSubCfg]
        simp [hempty]
      · intro i vm hi
        simp only [cleanSubCfg] at hi
        split_ifs at hi with hiW
        cases hi
        refine ⟨by simp [cleanSubCfg, cleanSubView, hiW], fun j => ?_, fun j hj => ?_⟩
        · by_cases hjW : j ∈ W <;> simp [cleanSubCfg, cleanSubView, hjW]
        · have hjW : j ∈ W := by by_contra h; simp [cleanSubCfg, h] at hj
          simp [cleanSubCfg, cleanSubView, hjW]

/-! ### Theorem 9 Part A: `C0` for non-decreasing positive crash schedules -/

theorem K_C0 {n : ℕ} :
    ∀ (r : ℕ) (State : Fin n → Type) [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
      (U : Finset (Fin n)) (ks : Fin r → ℕ),
      (∀ t, 1 ≤ ks t) →
      (∀ t₁ t₂ : Fin r, t₁ ≤ t₂ → ks t₁ ≤ ks t₂) →
      (∑ t, ks t) + 2 ≤ U.card →
      (∀ τ, (KSingle State U ks τ).C0) ∧ (KAll State U ks).C0
  | 0, State, _, _, U, ks, _, _, hU => by
      have h1 : 1 ≤ U.card := by simp at hU; omega
      have hSingle : ∀ τ, (KSingle State U ks τ).C0 := by
        intro τ
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
        exact (single_cfg_C1 (r := 0) (initConfig U τ) ⟨i₀, τ i₀, by simp [initConfig, hi₀]⟩).1
      refine ⟨hSingle, ?_⟩
      rw [KAll_eq_sUnion_InitCfg]
      refine SComplex.C0_sUnion_of_strictOrder cfgLt cfgLt_irrefl cfgLt_trans cfgLt_trich _
        (fun τ => hSingle τ.1) (fun τ ⟨σ, hστ⟩ => ?_)
      obtain ⟨p, _, hlt⟩ := hστ
      have hpU : p ∈ U := by
        by_contra hpU; rw [σ.2 p hpU, τ.2 p hpU] at hlt; exact Nat.lt_irrefl _ hlt
      let τ' : InitCfg State U := ⟨Function.update τ.1 p (σ.1 p), fun i hi => by
        have hip : i ≠ p := by intro h; subst h; exact hi hpU
        simp [Function.update, hip, τ.2 i hi]⟩
      have hlt' : cfgLt τ' τ := ⟨p, fun j hj => by
          have hjp : j ≠ p := ne_of_lt hj
          simp [τ', Function.update, hjp],
        by simp [τ', Function.update, hlt]⟩
      have hcard_erase : 1 ≤ (U.erase p).card := by
        rw [Finset.card_erase_of_mem hpU]; simp at hU; omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hcard_erase
      have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hqU : q ∈ U := (Finset.mem_erase.mp hq).2
      refine ⟨⟨q, τ.1 q⟩, ⟨τ', hlt', Finset.singleton_nonempty _, initConfig U τ'.1, rfl, ?_⟩,
        ⟨Finset.singleton_nonempty _, initConfig U τ.1, rfl, ?_⟩⟩
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl
        simp [initConfig, hqU, τ', Function.update, hqne]
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl
        simp [initConfig, hqU]
  | r + 1, State, _, _, U, ks, hpos, hmono, hU => by
      have hsum : ∑ t : Fin (r + 1), ks t = ks 0 + ∑ t : Fin r, ks t.succ := Fin.sum_univ_succ ks
      have hSingle : ∀ τ, (KSingle State U ks τ).C0 := by
        intro τ
        rw [KSingle_succ_eq U τ ks]
        let P_pred : Finset (Fin n) → Prop := fun W => W ⊆ U ∧ (U \ W).card ≤ ks 0
        let F_W : Finset (Fin n) → SComplex (Vert State (r + 1)) := fun W =>
          (KAll (Round1State State U W τ) W (fun t => ks t.succ)).mapInj (embedVert U W τ)
        have hF_W : ∀ W, P_pred W → (F_W W).C0 := by
          intro W ⟨hWU, hWcard⟩
          have hcardW : (∑ t : Fin r, ks t.succ) + 2 ≤ W.card := by
            have := Finset.card_sdiff_add_card_eq_card hWU
            omega
          have ihW := (K_C0 r (Round1State State U W τ) W (fun t => ks t.succ)
            (fun t => hpos t.succ)
            (fun t₁ t₂ h => hmono t₁.succ t₂.succ (Fin.succ_le_succ_iff.mpr h))
            hcardW).2
          exact SComplex.mapInj_C0 (embedVert_injective U W τ) ihW
        have hPU : P_pred U := ⟨Finset.Subset.refl U, by simp⟩
        have eq_union : SComplex.sUnion P_pred F_W = (F_W U).union (SComplex.sUnion P_pred F_W) := by
          ext s; simp only [SComplex.sUnion, SComplex.union]
          exact ⟨Or.inr, fun h => h.elim (fun hs => ⟨U, hPU, hs⟩) id⟩
        rw [eq_union]
        refine SComplex.C0_star_union (hF_W U hPU) hF_W (fun W ⟨hWU, hWcard⟩ => ?_)
        have hWpos : 1 ≤ W.card := by
          have := Finset.card_sdiff_add_card_eq_card hWU
          omega
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hWpos
        have h_embed_eq : ∀ {m : ℕ} (j : Fin n),
            embedView U U τ j (cleanSubView W (defaultR1 U U τ) m j) =
            embedView U W τ j (cleanSubView W (defaultR1 U W τ) m j) := by
          intro m
          induction m with
          | zero => intro j; rfl
          | succ m ihm =>
            intro j
            simp only [cleanSubView, embedView]
            refine Prod.ext (ihm j) ?_
            funext l; by_cases hl : l ∈ W <;> simp [hl, ihm l]
        refine ⟨⟨i₀, embedView U W τ i₀ (cleanSubView W (defaultR1 U W τ) r i₀)⟩, ?_, ?_⟩
        · change (F_W U).vert _
          dsimp only [F_W]
          rw [SComplex.mapInj_vert_iff (embedVert_injective U U τ)]
          refine ⟨⟨i₀, cleanSubView W (defaultR1 U U τ) r i₀⟩, ?_,
            Sigma.ext rfl (heq_of_eq (h_embed_eq i₀))⟩
          cases r with
          | zero =>
            refine ⟨Finset.singleton_nonempty _, initConfig U (defaultR1 U U τ),
              ⟨defaultR1 U U τ, rfl⟩, fun x hx => ?_⟩
            rcases Finset.mem_singleton.mp hx with rfl
            simp [initConfig, hWU hi₀, cleanSubView]
          | succ r' =>
            have hk01 : (U \ W).card ≤ ks (Fin.succ 0) :=
              hWcard.trans (hmono 0 (Fin.succ 0) (Fin.zero_le _))
            refine ⟨Finset.singleton_nonempty _, cleanSubCfg W (defaultR1 U U τ) (r' + 1),
              ⟨defaultR1 U U τ, FIReach_silentCrash_cleanSubCfg hWU (defaultR1 U U τ) _ hk01⟩,
              fun x hx => ?_⟩
            rcases Finset.mem_singleton.mp hx with rfl
            simp [cleanSubCfg, hi₀]
        · change (F_W W).vert _
          dsimp only [F_W]
          rw [SComplex.mapInj_vert_iff (embedVert_injective U W τ)]
          refine ⟨⟨i₀, cleanSubView W (defaultR1 U W τ) r i₀⟩, ?_, rfl⟩
          refine ⟨Finset.singleton_nonempty _, cleanSubCfg W (defaultR1 U W τ) r,
            ⟨defaultR1 U W τ, FIReach_cleanSubCfg W (defaultR1 U W τ) r _⟩, fun x hx => ?_⟩
          rcases Finset.mem_singleton.mp hx with rfl
          simp [cleanSubCfg, hi₀]
      refine ⟨hSingle, ?_⟩
      rw [KAll_eq_sUnion_InitCfg]
      refine SComplex.C0_sUnion_of_strictOrder cfgLt cfgLt_irrefl cfgLt_trans cfgLt_trich _
        (fun τ => hSingle τ.1) (fun τ ⟨σ, hστ⟩ => ?_)
      obtain ⟨p, _, hlt⟩ := hστ
      have hpU : p ∈ U := by
        by_contra hpU; rw [σ.2 p hpU, τ.2 p hpU] at hlt; exact Nat.lt_irrefl _ hlt
      let τ' : InitCfg State U := ⟨Function.update τ.1 p (σ.1 p), fun i hi => by
        have hip : i ≠ p := by intro h; subst h; exact hi hpU
        simp [Function.update, hip, τ.2 i hi]⟩
      have hlt' : cfgLt τ' τ := ⟨p, fun j hj => by
          have hjp : j ≠ p := ne_of_lt hj
          simp [τ', Function.update, hjp],
        by simp [τ', Function.update, hlt]⟩
      let W := U.erase p
      have hWU : W ⊆ U := Finset.erase_subset p U
      have hUW : (U \ W).card ≤ ks 0 := by
        have : U \ W = {p} := by ext i; by_cases hip : i = p <;> simp [W, hip, hpU]
        rw [this, Finset.card_singleton]; exact hpos 0
      have hWpos : 1 ≤ W.card := by
        rw [Finset.card_erase_of_mem hpU]; omega
      obtain ⟨q, hqW⟩ := Finset.card_pos.mp hWpos
      have h_view_eq : ∀ {m : ℕ} (j : Fin n), j ∈ W →
          cleanSubView W τ'.1 m j = cleanSubView W τ.1 m j := by
        intro m
        induction m with
        | zero =>
          intro j hjW
          have hjp : j ≠ p := (Finset.mem_erase.mp hjW).1
          simp [cleanSubView, τ', Function.update, hjp]
        | succ m ihm =>
          intro j hjW
          simp only [cleanSubView]
          refine Prod.ext (ihm j hjW) ?_
          funext l
          by_cases hl : l ∈ W
          · simp [hl, ihm l hl]
          · simp [hl]
      refine ⟨⟨q, cleanSubView W τ.1 (r + 1) q⟩,
        ⟨τ', hlt', Finset.singleton_nonempty _, cleanSubCfg W τ'.1 (r + 1),
          FIReach_silentCrash_cleanSubCfg hWU τ'.1 ks hUW, ?_⟩,
        ⟨Finset.singleton_nonempty _, cleanSubCfg W τ.1 (r + 1),
          FIReach_silentCrash_cleanSubCfg hWU τ.1 ks hUW, ?_⟩⟩
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl
        simp [cleanSubCfg, hqW, h_view_eq q hqW]
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl
        simp [cleanSubCfg, hqW]

/-! ### Theorem 9 Part B: `C1` for constant crash budget 2 -/

abbrev ks2 (r : ℕ) : Fin r → ℕ := fun _ => 2

abbrev ks12 (r' : ℕ) : Fin (r' + 1) → ℕ := Fin.cons 1 (ks2 r')

lemma ks12_pos {r' : ℕ} (t : Fin (r' + 1)) : 1 ≤ ks12 r' t := by
  cases t using Fin.cases with
  | zero => simp [ks12]
  | succ _ => simp [ks12, ks2]

lemma ks12_mono {r' : ℕ} (t₁ t₂ : Fin (r' + 1)) (h : t₁ ≤ t₂) : ks12 r' t₁ ≤ ks12 r' t₂ := by
  cases t₁ using Fin.cases <;> cases t₂ using Fin.cases
  · simp [ks12]
  · simp [ks12, ks2]
  · exfalso; exact not_lt_of_ge h (Fin.succ_pos _)
  · simp [ks12, ks2]

lemma ks12_sum (r' : ℕ) : ∑ t, ks12 r' t = 2 * r' + 1 := by
  rw [Fin.sum_univ_succ]
  simp [ks12, ks2]
  omega

lemma usesProc_mapView_iff {n : ℕ} {State₁ State₂ : Fin n → Type}
    (f : (i : Fin n) → State₁ i → State₂ i) {p : Fin n} :
    ∀ {r : ℕ} {i : Fin n} {w : View State₁ r i},
      usesProc p (mapView f i w) ↔ usesProc p w
  | 0, _, _ => Iff.rfl
  | _ + 1, _, (v, M) => by
      dsimp only [mapView, usesProc]
      refine or_congr (usesProc_mapView_iff f) ⟨?_, ?_⟩
      · rintro ⟨j, w', hjw', hp⟩
        obtain ⟨w₀, hjw₀, rfl⟩ := opt_map_eq_some.mp hjw'
        exact ⟨j, w₀, hjw₀, (usesProc_mapView_iff f).mp hp⟩
      · rintro ⟨j, w₀, hjw₀, hp⟩
        exact ⟨j, mapView f j w₀, by simp [hjw₀], (usesProc_mapView_iff f).mpr hp⟩

lemma usesProc_stripView_not {n : ℕ} {State : Fin n → Type} (q : Fin n) :
    ∀ {r : ℕ} {i : Fin n} {w : View State r i}, i ≠ q → ¬ usesProc q (stripView q i w)
  | 0, _, _, hne => hne
  | _ + 1, i, (v, M), hne => by
      rintro (hpv | ⟨j, w', hjw', hp⟩)
      · exact usesProc_stripView_not q hne hpv
      · dsimp only [stripView] at hjw'
        by_cases hjq : j = q
        · simp [hjq] at hjw'
        · simp only [hjq, ↓reduceIte] at hjw'
          obtain ⟨w₀, _, rfl⟩ := opt_map_eq_some.mp hjw'
          exact usesProc_stripView_not q hjq hp

lemma usesProc_of_embedView_eq {n : ℕ} {State : Fin n → Type}
    {U W₁ W₂ : Finset (Fin n)} {τ : (i : Fin n) → State i}
    {τ₁ : (i : Fin n) → Round1State State U W₁ τ i}
    {τ₂ : (i : Fin n) → Round1State State U W₂ τ i} {q : Fin n} :
    ∀ {m : ℕ} {i : Fin n}
      {v₁ : View (Round1State State U W₁ τ) m i}
      {v₂ : View (Round1State State U W₂ τ) m i},
      embedView U W₁ τ i v₁ = embedView U W₂ τ i v₂ →
      validFrom W₁ τ₁ v₁ → validFrom W₂ τ₂ v₂ →
      usesProc q v₂ →
      q ∈ W₁ ∧ q ∈ W₂ ∧ (τ₂ q).val = (τ₁ q).val
  | 0, i, v₁, v₂, hemb, hv₁, hv₂, hq => by
      subst hq
      have hval : v₁.val = v₂.val := (Prod.mk.inj hemb).2
      rw [hv₁.2, hv₂.2] at hval
      exact ⟨hv₁.1, hv₂.1, hval.symm⟩
  | _ + 1, i, (v₁, M₁), (v₂, M₂), hemb, hv₁, hv₂, hq => by
      obtain ⟨hemb_v, hemb_M⟩ := Prod.mk.inj hemb
      rcases hq with hqv | ⟨j, w₂, hjw₂, hqw⟩
      · exact usesProc_of_embedView_eq hemb_v hv₁.1 hv₂.1 hqv
      · have hj : (M₁ j).map (embedView U W₁ τ j) = (M₂ j).map (embedView U W₂ τ j) :=
          congr_fun hemb_M j
        rw [hjw₂, Option.map_some] at hj
        obtain ⟨w₁, hjw₁, hw_eq⟩ := opt_map_eq_some.mp hj
        exact usesProc_of_embedView_eq hw_eq (hv₁.2 j w₁ hjw₁) (hv₂.2 j w₂ hjw₂) hqw

def castR1 {n : ℕ} {State : Fin n → Type} {U W W' : Finset (Fin n)}
    (h : W' ⊆ W) {τ : (i : Fin n) → State i} (q : Fin n)
    (m : Round1State State U W τ q) : Round1State State U W' τ q :=
  ⟨m.1, m.2.1, fun j hj => m.2.2 j (h hj)⟩

lemma embedView_mapView_eq {n : ℕ} {State : Fin n → Type}
    {U W₁ W₂ : Finset (Fin n)} {τ : (i : Fin n) → State i}
    (g : (q : Fin n) → Round1State State U W₁ τ q → Round1State State U W₂ τ q)
    {V : Finset (Fin n)} {τ₁ : (q : Fin n) → Round1State State U W₁ τ q} :
    ∀ {m : ℕ} {i : Fin n} {w : View (Round1State State U W₁ τ) m i},
      validFrom V τ₁ w →
      (∀ q, usesProc q w → (g q (τ₁ q)).val = (τ₁ q).val) →
      embedView U W₂ τ i (mapView g i w) = embedView U W₁ τ i w
  | 0, i, w, hv, hg => by
      have hq : (g i (τ₁ i)).val = (τ₁ i).val := hg i rfl
      dsimp only [mapView, embedView]
      rw [hv.2, hq]
  | _ + 1, i, (v, M), hv, hg => by
      dsimp only [mapView, embedView]
      refine Prod.ext (embedView_mapView_eq g hv.1 (fun q h => hg q (Or.inl h))) ?_
      funext j
      dsimp only
      cases hMj : M j with
      | none => rfl
      | some wj =>
        simp only [Option.map_some, Option.some.injEq]
        exact embedView_mapView_eq g (hv.2 j wj hMj)
          (fun q h => hg q (Or.inr ⟨j, wj, hMj, h⟩))

lemma eq_defaultR1_of_U {n : ℕ} {State : Fin n → Type} (U : Finset (Fin n))
    (τ : (i : Fin n) → State i) (q : Fin n) (m : Round1State State U U τ q) :
    m = defaultR1 U U τ q := by
  apply Subtype.ext; funext j
  by_cases hjU : j ∈ U
  · exact m.2.2 j hjU
  · rcases m.2.1 j with h0 | h1
    · simp [defaultR1, initConfig, hjU, h0]
    · exact h1

/-- Key common extractor for `(P W₁) ∩ (P W₂)`: produces a witnessing execution over
`Round1State State U (W₁ ∪ W₂) τ` starting on `W₂`, where no vertex in the simplex uses any
process in `W₂ \ W₁`. -/
lemma inter_PW_extract {n : ℕ} {State : Fin n → Type} {U W₁ W₂ : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r : ℕ} {ks' : Fin r → ℕ} {s : Finset (Vert State (r + 1))}
    (hs₁ : ((KAll (Round1State State U W₁ τ) W₁ ks').mapInj (embedVert U W₁ τ)).mem s)
    (hs₂ : ((KAll (Round1State State U W₂ τ) W₂ ks').mapInj (embedVert U W₂ τ)).mem s) :
    ∃ (τ_u : (i : Fin n) → Round1State State U (W₁ ∪ W₂) τ i)
      (s_u : Finset (Vert (Round1State State U (W₁ ∪ W₂) τ) r))
      (c_u : (i : Fin n) → Option (View (Round1State State U (W₁ ∪ W₂) τ) r i)),
      s_u.Nonempty ∧
      (∀ y, y ∈ s ↔ ∃ x ∈ s_u, embedVert U (W₁ ∪ W₂) τ x = y) ∧
      FIReach r ks' (initConfig W₂ τ_u) c_u ∧
      (∀ x ∈ s_u, c_u x.1 = some x.2) ∧
      (∀ p, p ∈ W₂ → p ∉ W₁ → ∀ x ∈ s_u, ¬ usesProc p x.2) := by
  obtain ⟨s₁, ⟨_, c₁, ⟨τ₁, hreach₁⟩, hsc₁⟩, hiff₁⟩ := hs₁
  obtain ⟨s₂, ⟨hs₂ne, c₂, ⟨τ₂, hreach₂⟩, hsc₂⟩, hiff₂⟩ := hs₂
  let g : (q : Fin n) → Round1State State U W₂ τ q → Round1State State U (W₁ ∪ W₂) τ q :=
    fun q m =>
      if h : ∀ j ∈ W₁ ∪ W₂, m.val j = initConfig U τ j then ⟨m.val, m.2.1, h⟩
      else defaultR1 U (W₁ ∪ W₂) τ q
  have hx₂_props : ∀ x ∈ s₂, ∀ q, usesProc q x.2 →
      q ∈ W₁ ∧ q ∈ W₂ ∧ (g q (τ₂ q)).val = (τ₂ q).val := by
    rintro ⟨ix, vx⟩ hx₂ q hqx
    have hmem_s : embedVert U W₂ τ ⟨ix, vx⟩ ∈ s := (hiff₂ _).mpr ⟨⟨ix, vx⟩, hx₂, rfl⟩
    obtain ⟨⟨ix₁, vx₁⟩, hx₁, heq⟩ := (hiff₁ _).mp hmem_s
    obtain ⟨hidx, hv_heq⟩ := Sigma.mk.inj_iff.mp heq
    dsimp only at hidx; subst hidx
    rw [heq_eq_eq] at hv_heq
    have hv₁ := validFrom_of_FIReach hreach₁ ix₁ vx₁ (hsc₁ ⟨ix₁, vx₁⟩ hx₁)
    have hv₂ := validFrom_of_FIReach hreach₂ ix₁ vx (hsc₂ ⟨ix₁, vx⟩ hx₂)
    obtain ⟨hqW₁, hqW₂, hval_eq⟩ := usesProc_of_embedView_eq hv_heq hv₁ hv₂ hqx
    have hall : ∀ j ∈ W₁ ∪ W₂, (τ₂ q).val j = initConfig U τ j := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj₁ | hj₂
      · rw [hval_eq]; exact (τ₁ q).2.2 j hj₁
      · exact (τ₂ q).2.2 j hj₂
    refine ⟨hqW₁, hqW₂, ?_⟩
    change (if h : ∀ j ∈ W₁ ∪ W₂, (τ₂ q).val j = initConfig U τ j then (⟨(τ₂ q).val, (τ₂ q).2.1, h⟩ : Round1State State U (W₁ ∪ W₂) τ q) else defaultR1 U (W₁ ∪ W₂) τ q).val = (τ₂ q).val
    rw [dif_pos hall]
  let mapVert : Vert (Round1State State U W₂ τ) r → Vert (Round1State State U (W₁ ∪ W₂) τ) r :=
    fun x => ⟨x.1, mapView g x.1 x.2⟩
  let s_u := s₂.image mapVert
  obtain ⟨x₀, hx₀⟩ := hs₂ne
  refine ⟨fun q => g q (τ₂ q), s_u, fun i => (c₂ i).map (mapView g i),
    ⟨mapVert x₀, by simp only [s_u, Finset.mem_image]; exact ⟨x₀, hx₀, rfl⟩⟩,
    ?_, mapView_FIReach g hreach₂, ?_, ?_⟩
  · intro y
    rw [hiff₂ y]
    simp only [s_u, Finset.mem_image]
    constructor
    · rintro ⟨x, hx₂, rfl⟩
      refine ⟨mapVert x, ⟨x, hx₂, rfl⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact embedView_mapView_eq g (validFrom_of_FIReach hreach₂ x.1 x.2 (hsc₂ x hx₂))
        (fun q hq => (hx₂_props x hx₂ q hq).2.2)
    · rintro ⟨z, ⟨x, hx₂, rfl⟩, rfl⟩
      refine ⟨x, hx₂, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact (embedView_mapView_eq g (validFrom_of_FIReach hreach₂ x.1 x.2 (hsc₂ x hx₂))
        (fun q hq => (hx₂_props x hx₂ q hq).2.2)).symm
  · intro z hz
    simp only [s_u, Finset.mem_image] at hz
    obtain ⟨x, hx₂, rfl⟩ := hz
    simp [mapVert, hsc₂ x hx₂]
  · intro p hp₂ hp₁ z hz huse
    simp only [s_u, Finset.mem_image] at hz
    obtain ⟨x, hx₂, rfl⟩ := hz
    have huse' : usesProc p x.2 := (usesProc_mapView_iff g).mp huse
    exact hp₁ (hx₂_props x hx₂ p huse').1

/-- Helper: lifting a sub-execution along `castR1` and `FIReach_mono`. -/
lemma mem_PW_of_castR1 {n : ℕ} {State : Fin n → Type} {U W W_big : Finset (Fin n)}
    (hsub : W ⊆ W_big) {τ : (i : Fin n) → State i} {r : ℕ} {ks₁ ks₂ : Fin r → ℕ}
    (hks : ∀ t, ks₁ t ≤ ks₂ t) {s : Finset (Vert State (r + 1))}
    (hs : ((KAll (Round1State State U W_big τ) W ks₁).mapInj (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W τ) W ks₂).mapInj (embedVert U W τ)).mem s := by
  obtain ⟨s₀, ⟨⟨x₀, hx₀⟩, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, hiff₀⟩ := hs
  let f := castR1 (U := U) (τ := τ) hsub
  let fVert : Vert (Round1State State U W_big τ) r → Vert (Round1State State U W τ) r :=
    fun x => ⟨x.1, mapView f x.1 x.2⟩
  refine ⟨s₀.image fVert,
    ⟨⟨fVert x₀, by simp only [Finset.mem_image]; exact ⟨x₀, hx₀, rfl⟩⟩,
     fun i => (c₀ i).map (mapView f i),
     ⟨fun i => f i (τ₀ i), FIReach_mono hks (mapView_FIReach f hreach₀)⟩, ?_⟩, ?_⟩
  · intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    simp [fVert, hsc₀ x hx]
  · intro y
    rw [hiff₀ y]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fVert x, ⟨x, hx, rfl⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact embedView_mapView_eq f (validFrom_of_FIReach hreach₀ x.1 x.2 (hsc₀ x hx)) (fun _ _ => rfl)
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact (embedView_mapView_eq f (validFrom_of_FIReach hreach₀ x.1 x.2 (hsc₀ x hx)) (fun _ _ => rfl)).symm

/-! Orderings for Stage 1 and Stage 2 of `KSingle_C1` -/

def optFinLt {n : ℕ} {P : Fin n → Prop} : Option { x : Fin n // P x } → Option { x : Fin n // P x } → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some x, some y => x.1 < y.1

lemma optFinLt_irrefl {n : ℕ} {P : Fin n → Prop} (a : Option { x : Fin n // P x }) : ¬ optFinLt a a := by
  cases a <;> simp [optFinLt]

lemma optFinLt_trans {n : ℕ} {P : Fin n → Prop} (a b c : Option { x : Fin n // P x }) :
    optFinLt a b → optFinLt b c → optFinLt a c := by
  cases a <;> cases b <;> cases c <;> simp [optFinLt]
  exact lt_trans

lemma optFinLt_trich {n : ℕ} {P : Fin n → Prop} (a b : Option { x : Fin n // P x }) :
    optFinLt a b ∨ a = b ∨ optFinLt b a := by
  cases a with
  | none => cases b with | none => exact Or.inr (Or.inl rfl) | some _ => exact Or.inl trivial
  | some x =>
    cases b with
    | none => exact Or.inr (Or.inr trivial)
    | some y =>
      rcases lt_trichotomy x.1 y.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (congrArg some (Subtype.ext h)))
      · exact Or.inr (Or.inr h)

abbrev PairIn {n : ℕ} (U : Finset (Fin n)) := { p : Fin n × Fin n // p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 < p.2 }

def optPairLt {n : ℕ} {U : Finset (Fin n)} : Option (PairIn U) → Option (PairIn U) → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some p, some q => p.1.1 < q.1.1 ∨ (p.1.1 = q.1.1 ∧ p.1.2 < q.1.2)

lemma optPairLt_irrefl {n : ℕ} {U : Finset (Fin n)} (a : Option (PairIn U)) : ¬ optPairLt a a := by
  cases a <;> simp [optPairLt]

lemma optPairLt_trans {n : ℕ} {U : Finset (Fin n)} (a b c : Option (PairIn U)) :
    optPairLt a b → optPairLt b c → optPairLt a c := by
  cases a <;> cases b <;> cases c <;> simp [optPairLt]
  rintro (h1 | ⟨e1, h1⟩) (h2 | ⟨e2, h2⟩)
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1.symm ▸ h2)
  · exact Or.inr ⟨e1.trans e2, lt_trans h1 h2⟩

lemma optPairLt_trich {n : ℕ} {U : Finset (Fin n)} (a b : Option (PairIn U)) :
    optPairLt a b ∨ a = b ∨ optPairLt b a := by
  cases a with
  | none => cases b with | none => exact Or.inr (Or.inl rfl) | some _ => exact Or.inl trivial
  | some p =>
    cases b with
    | none => exact Or.inr (Or.inr trivial)
    | some q =>
      rcases lt_trichotomy p.1.1 q.1.1 with h1 | e1 | h1
      · exact Or.inl (Or.inl h1)
      · rcases lt_trichotomy p.1.2 q.1.2 with h2 | e2 | h2
        · exact Or.inl (Or.inr ⟨e1, h2⟩)
        · exact Or.inr (Or.inl (congrArg some (Subtype.ext (Prod.ext e1 e2))))
        · exact Or.inr (Or.inr (Or.inr ⟨e1.symm, h2⟩))
      · exact Or.inr (Or.inr (Or.inl h1))

/-! Helper for `KAll` intersection with `cfgLt` predecessors -/

lemma KAll_inter_lt_eq_zero {n : ℕ} {State : Fin n → Type}
    [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} (ks : Fin 0 → ℕ) (τ : InitCfg State U) :
    (SComplex.sUnion (fun σ : InitCfg State U => cfgLt σ τ)
      (fun σ => KSingle State U ks σ.1)).inter (KSingle State U ks τ.1) =
    SComplex.sUnion (fun p : Fin n => p ∈ U ∧ ∃ s₀ : State p, stateRank State p s₀ < stateRank State p (τ.1 p))
      (fun p => KSingle State (U.erase p) ks τ.1) := by
  ext s
  simp only [SComplex.inter, SComplex.sUnion, KSingle, genComplex]
  constructor
  · rintro ⟨⟨σ, ⟨p, heq, hlt⟩, hsne, c₁, rfl, hsc₁⟩, ⟨_, c₂, rfl, hsc₂⟩⟩
    have hpU : p ∈ U := by
      by_contra hpU; rw [σ.2 p hpU, τ.2 p hpU] at hlt; exact Nat.lt_irrefl _ hlt
    refine ⟨p, ⟨hpU, σ.1 p, hlt⟩, hsne, initConfig (U.erase p) τ.1, rfl, ?_⟩
    intro x hx
    have h1 := hsc₁ x hx
    have h2 := hsc₂ x hx
    have hxp : x.1 ≠ p := by
      intro hxp; subst hxp
      simp only [initConfig, hpU, ↓reduceIte, Option.some.injEq] at h1 h2
      rw [h1, h2] at hlt
      exact Nat.lt_irrefl _ hlt
    simpa [initConfig, Finset.mem_erase, hxp] using h2
  · rintro ⟨p, ⟨hpU, s₀, hlt⟩, hsne, c, rfl, hsc⟩
    let σ : InitCfg State U := ⟨Function.update τ.1 p s₀, fun i hi => by
      have hip : i ≠ p := by intro h; subst h; exact hi hpU
      simp [Function.update, hip, τ.2 i hi]⟩
    have hστ : cfgLt σ τ := ⟨p, fun j hj => by
        have hjp : j ≠ p := ne_of_lt hj
        simp [σ, Function.update, hjp],
      by simp [σ, Function.update, hlt]⟩
    refine ⟨⟨σ, hστ, hsne, initConfig U σ.1, rfl, ?_⟩, ⟨hsne, initConfig U τ.1, rfl, ?_⟩⟩
    · intro x hx
      have h := hsc x hx
      have hxp : x.1 ≠ p := by intro e; subst e; simp [initConfig] at h
      have hxU : x.1 ∈ U := by by_contra hnU; simp [initConfig, hnU] at h
      rw [initConfig, if_pos (Finset.mem_erase.mpr ⟨hxp, hxU⟩), Option.some.injEq] at h
      rw [initConfig, if_pos hxU, Option.some.injEq, ← h]
      simp [σ, Function.update, hxp]
    · intro x hx
      have h := hsc x hx
      have hxp : x.1 ≠ p := by intro e; subst e; simp [initConfig] at h
      have hxU : x.1 ∈ U := by by_contra hnU; simp [initConfig, hnU] at h
      rw [initConfig, if_pos (Finset.mem_erase.mpr ⟨hxp, hxU⟩), Option.some.injEq] at h
      rw [initConfig, if_pos hxU, Option.some.injEq, ← h]

lemma KAll_inter_lt_eq_succ {n : ℕ} {State : Fin n → Type}
    [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
    {U : Finset (Fin n)} {r : ℕ} (τ : InitCfg State U) :
    (SComplex.sUnion (fun σ : InitCfg State U => cfgLt σ τ)
      (fun σ => KSingle State U (ks2 (r + 1)) σ.1)).inter (KSingle State U (ks2 (r + 1)) τ.1) =
    SComplex.sUnion (fun p : Fin n => p ∈ U ∧ ∃ s₀ : State p, stateRank State p s₀ < stateRank State p (τ.1 p))
      (fun p => KSingle State (U.erase p) (ks12 r) τ.1) := by
  ext s
  simp only [SComplex.inter, SComplex.sUnion, KSingle, genComplex]
  constructor
  · rintro ⟨⟨σ, ⟨p, _, hlt⟩, hsne, c₁, hreach₁, hsc₁⟩, ⟨_, c₂, hreach₂, hsc₂⟩⟩
    have hpU : p ∈ U := by
      by_contra hpU; rw [σ.2 p hpU, τ.2 p hpU] at hlt; exact Nat.lt_irrefl _ hlt
    have hp_ne : σ.1 p ≠ τ.1 p := fun e => Nat.ne_of_lt hlt (congrArg _ e)
    obtain ⟨x₀, hx₀⟩ := hsne
    have hsne' : s.Nonempty := ⟨x₀, hx₀⟩
    have hnot : ∀ x ∈ s, ¬ usesProc p x.2 := by
      intro x hx huse
      have hv₁ := validFrom_of_FIReach hreach₁ x.1 x.2 (hsc₁ x hx)
      have hv₂ := validFrom_of_FIReach hreach₂ x.1 x.2 (hsc₂ x hx)
      exact hp_ne (usesProc_agree hv₁ hv₂ huse)
    have hstrip := strip_FIReach hpU (by simp [ks2]) hreach₂ ⟨x₀.1, x₀.2, hsc₂ x₀ hx₀, hnot x₀ hx₀⟩
    refine ⟨p, ⟨hpU, σ.1 p, hlt⟩, hsne',
      fun i => if i = p then none else (c₂ i).map (stripView p i), hstrip.2, ?_⟩
    intro x hx
    have hxp : x.1 ≠ p := fun e => by
      have hnotx := hnot x hx
      subst e; exact hnotx (usesProc_self x.1 x.2)
    simp [hxp, hsc₂ x hx, stripView_eq_of_not_usesProc p (hnot x hx)]
  · rintro ⟨p, ⟨hpU, s₀, hlt⟩, hsne, c, hreach, hsc⟩
    let σ : InitCfg State U := ⟨Function.update τ.1 p s₀, fun i hi => by
      have hip : i ≠ p := by intro h; subst h; exact hi hpU
      simp [Function.update, hip, τ.2 i hi]⟩
    have hστ : cfgLt σ τ := ⟨p, fun j hj => by
        have hjp : j ≠ p := ne_of_lt hj
        simp [σ, Function.update, hjp],
      by simp [σ, Function.update, hlt]⟩
    have hreach_τ : FIReach (r + 1) (ks2 (r + 1)) (initConfig U τ.1) c := by
      have eq_ks : Fin.cons 2 (ks2 r) = ks2 (r + 1) := by
        funext t; cases t using Fin.cases <;> rfl
      rw [← eq_ks]
      exact unstrip_FIReach hpU (by omega) hreach
    let f : (i : Fin n) → State i → State i := fun i x =>
      if h : i = p then h ▸ s₀ else x
    have hf_τ : (fun i => f i (τ.1 i)) = σ.1 := by
      funext i; by_cases hip : i = p
      · subst hip; simp [f, σ, Function.update]
      · simp [f, σ, Function.update, hip]
    have hreach_σ : FIReach (r + 1) (ks2 (r + 1)) (initConfig U σ.1)
        (fun i => (c i).map (mapView f i)) := hf_τ ▸ mapView_FIReach f hreach_τ
    refine ⟨⟨σ, hστ, hsne, fun i => (c i).map (mapView f i), hreach_σ, ?_⟩,
      ⟨hsne, c, hreach_τ, hsc⟩⟩
    intro x hx
    have hv_erase := validFrom_of_FIReach hreach x.1 x.2 (hsc x hx)
    have hfx : mapView f x.1 x.2 = x.2 := by
      refine mapView_id_of_validFrom f (validFrom_of_FIReach hreach_τ x.1 x.2 (hsc x hx)) ?_
      intro q huse
      have hq_mem : q ∈ U.erase p := usesProc_validFrom hv_erase huse
      have hqp : q ≠ p := (Finset.mem_erase.mp hq_mem).1
      simp [f, hqp]
    simp [hsc x hx, hfx]

lemma sub_subsets_le_two {n : ℕ} {V : Type*} (U : Finset (Fin n))
    (F : Finset (Fin n) → SComplex V) :
    SComplex.sUnion (fun W => W ⊆ U ∧ (U \ W).card ≤ 2) F =
      SComplex.sUnion (fun _ : Option (PairIn U) => True)
        (fun
          | none => SComplex.sUnion (fun _ : Option { x : Fin n // x ∈ U } => True)
              (fun | none => F U | some x => F (U.erase x.1))
          | some p => F ((U.erase p.1.1).erase p.1.2)) := by
  ext s
  simp only [SComplex.sUnion, true_and]
  constructor
  · rintro ⟨W, ⟨hWU, hcard⟩, hs⟩
    have hW_eq : W = U \ (U \ W) := by
      ext z; by_cases hzU : z ∈ U <;> by_cases hzW : z ∈ W
      · simp [hzU, hzW]
      · simp [hzU, hzW]
      · exfalso; exact hzU (hWU hzW)
      · simp [hzU, hzW]
    have hD : (U \ W).card = 0 ∨ (U \ W).card = 1 ∨ (U \ W).card = 2 := by omega
    rcases hD with h0 | h1 | h2
    · have hemp : U \ W = ∅ := Finset.card_eq_zero.mp h0
      have : W = U := by rw [hW_eq, hemp, Finset.sdiff_empty]
      subst this
      exact ⟨none, none, hs⟩
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      have hxU : x ∈ U := by
        have : x ∈ U \ W := hx ▸ Finset.mem_singleton_self x
        exact (Finset.mem_sdiff.mp this).1
      have : W = U.erase x := by
        rw [hW_eq, hx]; ext z; simp [Finset.mem_erase, and_comm]
      subst this
      exact ⟨none, some ⟨x, hxU⟩, hs⟩
    · obtain ⟨a, b, hab, hab_eq⟩ := Finset.card_eq_two.mp h2
      have ha_in : a ∈ U \ W := hab_eq ▸ Finset.mem_insert_self a {b}
      have hb_in : b ∈ U \ W := hab_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have haU : a ∈ U := (Finset.mem_sdiff.mp ha_in).1
      have hbU : b ∈ U := (Finset.mem_sdiff.mp hb_in).1
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have : W = (U.erase a).erase b := by
          rw [hW_eq, hab_eq]; ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
          tauto
        subst this
        exact ⟨some ⟨(a, b), haU, hbU, hlt⟩, hs⟩
      · have : W = (U.erase b).erase a := by
          rw [hW_eq, hab_eq]; ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
          tauto
        subst this
        exact ⟨some ⟨(b, a), hbU, haU, hgt⟩, hs⟩
  · rintro ⟨optP, hs⟩
    cases optP with
    | none =>
      obtain ⟨optX, hs⟩ := hs
      cases optX with
      | none => exact ⟨U, ⟨Finset.Subset.refl U, by simp⟩, hs⟩
      | some x =>
        refine ⟨U.erase x.1, ⟨Finset.erase_subset _ _, ?_⟩, hs⟩
        have hsub : U \ U.erase x.1 ⊆ {x.1} := by
          intro z hz; simp only [Finset.mem_sdiff, Finset.mem_erase] at hz
          simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
        exact (Finset.card_le_card hsub).trans (by simp)
    | some p =>
      refine ⟨(U.erase p.1.1).erase p.1.2,
        ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩, hs⟩
      have hsub : U \ (U.erase p.1.1).erase p.1.2 ⊆ {p.1.1, p.1.2} := by
        intro z hz
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        by_contra h
        push Not at h
        exact hz.2 ⟨h.2, h.1, hz.1⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- Helper: stripping one unused process from a `ks2 (r' + 1)` execution into `ks12 r'`. -/
lemma strip1_mem_KSingle {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r' : ℕ}
    {τ_u : (i : Fin n) → Round1State State U W_big τ i}
    {s_u : Finset (Vert (Round1State State U W_big τ) (r' + 1))}
    {c_u : (i : Fin n) → Option (View (Round1State State U W_big τ) (r' + 1) i)}
    {s : Finset (Vert State (r' + 2))} {p : Fin n}
    (hpV : p ∈ V) (hs_ne : s_u.Nonempty) (himg : ∀ y, y ∈ s ↔ ∃ x ∈ s_u, embedVert U W_big τ x = y)
    (hreach : FIReach (r' + 1) (ks2 (r' + 1)) (initConfig V τ_u) c_u)
    (hsc : ∀ x ∈ s_u, c_u x.1 = some x.2)
    (hnot : ∀ x ∈ s_u, ¬ usesProc p x.2) :
    ((KSingle (Round1State State U W_big τ) (V.erase p) (ks12 r') τ_u).mapInj
      (embedVert U W_big τ)).mem s := by
  obtain ⟨x₀, hx₀⟩ := hs_ne
  have hst := strip_FIReach hpV (by simp [ks2]) hreach ⟨x₀.1, x₀.2, hsc x₀ hx₀, hnot x₀ hx₀⟩
  refine ⟨s_u, ⟨⟨x₀, hx₀⟩, fun i => if i = p then none else (c_u i).map (stripView p i),
    hst.2, ?_⟩, himg⟩
  intro x hx
  have hxp : x.1 ≠ p := fun e => by
    have hn := hnot x hx; subst e; exact hn (usesProc_self x.1 x.2)
  simp [hxp, hsc x hx, stripView_eq_of_not_usesProc p (hnot x hx)]

/-- Helper: stripping two unused processes from `ks2 (r' + 1)` into `Fin.cons 0 (ks2 r')`. -/
lemma strip2_mem_KSingle {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r' : ℕ}
    {τ_u : (i : Fin n) → Round1State State U W_big τ i}
    {s_u : Finset (Vert (Round1State State U W_big τ) (r' + 1))}
    {c_u : (i : Fin n) → Option (View (Round1State State U W_big τ) (r' + 1) i)}
    {s : Finset (Vert State (r' + 2))} {p q : Fin n}
    (hpV : p ∈ V) (hqV : q ∈ V.erase p)
    (hs_ne : s_u.Nonempty) (himg : ∀ y, y ∈ s ↔ ∃ x ∈ s_u, embedVert U W_big τ x = y)
    (hreach : FIReach (r' + 1) (ks2 (r' + 1)) (initConfig V τ_u) c_u)
    (hsc : ∀ x ∈ s_u, c_u x.1 = some x.2)
    (hnotp : ∀ x ∈ s_u, ¬ usesProc p x.2)
    (hnotq : ∀ x ∈ s_u, ¬ usesProc q x.2) :
    ((KSingle (Round1State State U W_big τ) ((V.erase p).erase q) (Fin.cons 0 (ks2 r')) τ_u).mapInj
      (embedVert U W_big τ)).mem s := by
  obtain ⟨x₀, hx₀⟩ := hs_ne
  have hst1 := strip_FIReach hpV (by simp [ks2]) hreach ⟨x₀.1, x₀.2, hsc x₀ hx₀, hnotp x₀ hx₀⟩
  let c₁ := fun i => if i = p then none else (c_u i).map (stripView p i)
  have hsc₁ : ∀ x ∈ s_u, c₁ x.1 = some x.2 := by
    intro x hx
    have hxp : x.1 ≠ p := fun e => by
      have hn := hnotp x hx; subst e; exact hn (usesProc_self x.1 x.2)
    simp [c₁, hxp, hsc x hx, stripView_eq_of_not_usesProc p (hnotp x hx)]
  have hst1_reach : FIReach (r' + 1) (ks12 r') (initConfig (V.erase p) τ_u) c₁ := hst1.2
  have hst2 := strip_FIReach hqV (by simp [ks12]) hst1_reach ⟨x₀.1, x₀.2, hsc₁ x₀ hx₀, hnotq x₀ hx₀⟩
  have eq_ks : Fin.cons (α := fun _ => ℕ) (ks12 r' 0 - 1) (fun t => ks12 r' t.succ) =
      Fin.cons (α := fun _ => ℕ) 0 (ks2 r') := by
    funext t; cases t using Fin.cases <;> rfl
  refine ⟨s_u, ⟨⟨x₀, hx₀⟩, fun i => if i = q then none else (c₁ i).map (stripView q i),
    eq_ks ▸ hst2.2, ?_⟩, himg⟩
  intro x hx
  have hxq : x.1 ≠ q := fun e => by
    have hn := hnotq x hx; subst e; exact hn (usesProc_self x.1 x.2)
  simp [hxq, hsc₁ x hx, stripView_eq_of_not_usesProc q (hnotq x hx)]

lemma KSingle_le_KAll_mapInj {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r : ℕ} {ks : Fin r → ℕ}
    {τ_u : (i : Fin n) → Round1State State U W_big τ i} {s : Finset (Vert State (r + 1))}
    (h : ((KSingle (Round1State State U W_big τ) V ks τ_u).mapInj (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W_big τ) V ks).mapInj (embedVert U W_big τ)).mem s := by
  obtain ⟨s₀, ⟨hne, c₀, hreach₀, hsc₀⟩, himg⟩ := h
  exact ⟨s₀, ⟨hne, c₀, ⟨τ_u, hreach₀⟩, hsc₀⟩, himg⟩

lemma unstrip_KAll_mapInj {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r' : ℕ} {k₀' k₀ : ℕ} (hk : k₀' + 1 ≤ k₀) {ks' : Fin r' → ℕ}
    {p : Fin n} (hpV : p ∈ V) {s : Finset (Vert State (r' + 2))}
    (h : ((KAll (Round1State State U W_big τ) (V.erase p) (Fin.cons k₀' ks')).mapInj
      (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W_big τ) V (Fin.cons k₀ ks')).mapInj
      (embedVert U W_big τ)).mem s := by
  obtain ⟨s₀, ⟨hne, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, himg⟩ := h
  exact ⟨s₀, ⟨hne, c₀, ⟨τ₀, unstrip_FIReach hpV hk hreach₀⟩, hsc₀⟩, himg⟩

lemma unstrip_KSingle_mapInj {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r' : ℕ} {k₀' k₀ : ℕ} (hk : k₀' + 1 ≤ k₀) {ks' : Fin r' → ℕ}
    {τ₀ : (i : Fin n) → Round1State State U W_big τ i}
    {p : Fin n} (hpV : p ∈ V) {s : Finset (Vert State (r' + 2))}
    (h : ((KSingle (Round1State State U W_big τ) (V.erase p) (Fin.cons k₀' ks') τ₀).mapInj
      (embedVert U W_big τ)).mem s) :
    ((KSingle (Round1State State U W_big τ) V (Fin.cons k₀ ks') τ₀).mapInj
      (embedVert U W_big τ)).mem s := by
  obtain ⟨s₀, ⟨hne, c₀, hreach₀, hsc₀⟩, himg⟩ := h
  exact ⟨s₀, ⟨hne, c₀, unstrip_FIReach hpV hk hreach₀, hsc₀⟩, himg⟩

lemma mono_KAll_mapInj {n : ℕ} {State : Fin n → Type} {U W_big V : Finset (Fin n)}
    {τ : (i : Fin n) → State i} {r : ℕ} {ks₁ ks₂ : Fin r → ℕ} (hks : ∀ t, ks₁ t ≤ ks₂ t)
    {s : Finset (Vert State (r + 1))}
    (h : ((KAll (Round1State State U W_big τ) V ks₁).mapInj (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W_big τ) V ks₂).mapInj (embedVert U W_big τ)).mem s := by
  obtain ⟨s₀, ⟨hne, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, himg⟩ := h
  exact ⟨s₀, ⟨hne, c₀, ⟨τ₀, FIReach_mono hks hreach₀⟩, hsc₀⟩, himg⟩

lemma cast_KAll_mapInj {n : ℕ} {State : Fin n → Type} {U W_small W_big V : Finset (Fin n)}
    (hsub : W_small ⊆ W_big) {τ : (i : Fin n) → State i} {r : ℕ} {ks : Fin r → ℕ}
    {s : Finset (Vert State (r + 1))}
    (h : ((KAll (Round1State State U W_big τ) V ks).mapInj (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W_small τ) V ks).mapInj (embedVert U W_small τ)).mem s := by
  obtain ⟨s₀, ⟨⟨x₀, hx₀⟩, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, hiff₀⟩ := h
  let f := castR1 (U := U) (τ := τ) hsub
  let fVert : Vert (Round1State State U W_big τ) r → Vert (Round1State State U W_small τ) r :=
    fun x => ⟨x.1, mapView f x.1 x.2⟩
  refine ⟨s₀.image fVert,
    ⟨⟨fVert x₀, by simp only [Finset.mem_image]; exact ⟨x₀, hx₀, rfl⟩⟩,
     fun i => (c₀ i).map (mapView f i),
     ⟨fun i => f i (τ₀ i), mapView_FIReach f hreach₀⟩, ?_⟩, ?_⟩
  · intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    simp [fVert, hsc₀ x hx]
  · intro y
    rw [hiff₀ y]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fVert x, ⟨x, hx, rfl⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact embedView_mapView_eq f (validFrom_of_FIReach hreach₀ x.1 x.2 (hsc₀ x hx)) (fun _ _ => rfl)
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, Sigma.ext rfl (heq_of_eq ?_)⟩
      exact (embedView_mapView_eq f (validFrom_of_FIReach hreach₀ x.1 x.2 (hsc₀ x hx)) (fun _ _ => rfl)).symm

lemma sub_KAll_zero_mapInj {n : ℕ} {State : Fin n → Type} {U W_big V₁ V₂ : Finset (Fin n)}
    (hV : V₁ ⊆ V₂) {τ : (i : Fin n) → State i} {ks : Fin 0 → ℕ}
    {s : Finset (Vert State 1)}
    (h : ((KAll (Round1State State U W_big τ) V₁ ks).mapInj (embedVert U W_big τ)).mem s) :
    ((KAll (Round1State State U W_big τ) V₂ ks).mapInj (embedVert U W_big τ)).mem s := by
  obtain ⟨s₀, ⟨hne, c₀, ⟨τ₀, rfl⟩, hsc₀⟩, himg⟩ := h
  refine ⟨s₀, ⟨hne, initConfig V₂ τ₀, ⟨τ₀, rfl⟩, ?_⟩, himg⟩
  intro x hx
  have hx0 := hsc₀ x hx
  have hxV₁ : x.1 ∈ V₁ := by by_contra hn; simp [initConfig, hn] at hx0
  have hxV₂ : x.1 ∈ V₂ := hV hxV₁
  simpa [initConfig, hxV₁, hxV₂] using hx0

private lemma erase_comm_eq {α : Type*} [DecidableEq α] (s : Finset α) (a b : α) :
    (s.erase a).erase b = (s.erase b).erase a := by
  ext z; simp [Finset.mem_erase, and_left_comm]

theorem K_C1 {n : ℕ} :
    ∀ (r : ℕ) (State : Fin n → Type) [∀ i, Fintype (State i)] [∀ i, Nonempty (State i)]
      (U : Finset (Fin n)),
      2 * r + 3 ≤ U.card →
      (∀ τ, (KSingle State U (ks2 r) τ).C1) ∧ (KAll State U (ks2 r)).C1
  | 0, State, _, _, U, hU => by
      have hSingle : ∀ τ, (KSingle State U (ks2 0) τ).C1 := by
        intro τ
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 1 ≤ U.card)
        exact single_cfg_C1 (r := 0) (initConfig U τ) ⟨i₀, τ i₀, by simp [initConfig, hi₀]⟩
      refine ⟨hSingle, ?_⟩
      rw [KAll_eq_sUnion_InitCfg]
      refine SComplex.C1_sUnion_of_strictOrder cfgLt cfgLt_irrefl cfgLt_trans cfgLt_trich _
        (fun τ => hSingle τ.1) (fun τ ⟨σ, hστ⟩ => ?_)
      rw [KAll_inter_lt_eq_zero]
      obtain ⟨p₀, _, hlt₀⟩ := hστ
      have hp₀U : p₀ ∈ U := by
        by_contra h; rw [σ.2 p₀ h, τ.2 p₀ h] at hlt₀; exact Nat.lt_irrefl _ hlt₀
      let P_idx : Fin n → Prop := fun p => p ∈ U ∧ ∃ s₀ : State p, stateRank State p s₀ < stateRank State p (τ.1 p)
      let B_p : Fin n → SComplex (Vert State 0) := fun p => KSingle State (U.erase p) (ks2 0) τ.1
      have hp₀ : P_idx p₀ := ⟨hp₀U, σ.1 p₀, hlt₀⟩
      have eq_u : SComplex.sUnion P_idx B_p = (B_p p₀).union (SComplex.sUnion P_idx B_p) := by
        ext s; simp only [SComplex.sUnion, SComplex.union]
        exact ⟨Or.inr, fun h => h.elim (fun hs => ⟨p₀, hp₀, hs⟩) id⟩
      rw [eq_u]
      have hBp_C0 : ∀ p, P_idx p → (B_p p).C0 := by
        intro p ⟨hpU, _⟩
        have h1 : 1 ≤ (U.erase p).card := by rw [Finset.card_erase_of_mem hpU]; omega
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
        exact (single_cfg_C1 (r := 0) (initConfig (U.erase p) τ.1) ⟨i₀, τ.1 i₀, by simp [initConfig, hi₀]⟩).1
      refine SComplex.C0_star_union (hBp_C0 p₀ hp₀) hBp_C0 (fun p ⟨hpU, _⟩ => ?_)
      have hcard2 : 1 ≤ ((U.erase p₀).erase p).card := by
        have h1 : (U.erase p₀).card = U.card - 1 := Finset.card_erase_of_mem hp₀U
        have h2 : (U.erase p₀).card - 1 ≤ ((U.erase p₀).erase p).card := Finset.pred_card_le_card_erase
        omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hcard2
      have hq1 : q ∈ U.erase p₀ := Finset.mem_of_mem_erase hq
      have hq2 : q ∈ U.erase p := by
        rw [erase_comm_eq] at hq; exact Finset.mem_of_mem_erase hq
      refine ⟨⟨q, τ.1 q⟩, ⟨Finset.singleton_nonempty _, initConfig (U.erase p₀) τ.1, rfl, ?_⟩,
        ⟨Finset.singleton_nonempty _, initConfig (U.erase p) τ.1, rfl, ?_⟩⟩
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl; simp [initConfig, hq1]
      · intro x hx; rcases Finset.mem_singleton.mp hx with rfl; simp [initConfig, hq2]
  | r + 1, State, _, _, U, hU => by
      have hSingle : ∀ τ, (KSingle State U (ks2 (r + 1)) τ).C1 := by
        intro τ
        have eq_succ : (fun t : Fin r => ks2 (r + 1) t.succ) = ks2 r := rfl
        rw [KSingle_succ_eq U τ (ks2 (r + 1)), eq_succ]
        let P_W : Finset (Fin n) → SComplex (Vert State (r + 1)) := fun W =>
          (KAll (Round1State State U W τ) W (ks2 r)).mapInj (embedVert U W τ)
        have hPW_C1 : ∀ W, W ⊆ U → (U \ W).card ≤ 2 → (P_W W).C1 := by
          intro W hWU hWcard
          have hcardW : 2 * r + 3 ≤ W.card := by
            have := Finset.card_sdiff_add_card_eq_card hWU
            omega
          exact SComplex.mapInj_C1 (embedVert_injective U W τ)
            (K_C1 r (Round1State State U W τ) W hcardW).2
        change (SComplex.sUnion (fun W => W ⊆ U ∧ (U \ W).card ≤ 2) P_W).C1
        rw [sub_subsets_le_two U P_W]
        -- Stage 1: K₁ = P_W U ∪ ⋃_{x ∈ U} P_W (U.erase x) is C1
        let F₁ : Option { x : Fin n // x ∈ U } → SComplex (Vert State (r + 1)) :=
          fun | none => P_W U | some x => P_W (U.erase x.1)
        have hK₁_C1 : (SComplex.sUnion (fun _ => True) F₁).C1 := by
          refine SComplex.C1_sUnion_of_strictOrder optFinLt optFinLt_irrefl optFinLt_trans optFinLt_trich F₁
            (fun | none => hPW_C1 U (Finset.Subset.refl U) (by simp)
                 | some x => hPW_C1 (U.erase x.1) (Finset.erase_subset _ _) (by
                     have hsub : U \ U.erase x.1 ⊆ {x.1} := by
                       intro z hz; simp only [Finset.mem_sdiff, Finset.mem_erase] at hz
                       simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
                     exact (Finset.card_le_card hsub).trans (by simp)))
            (fun a hex => ?_)
          cases a with
          | none => obtain ⟨b, hb⟩ := hex; cases b <;> simp [optFinLt] at hb
          | some x =>
            obtain ⟨x, hxU⟩ := x
            dsimp only [F₁]
            cases r with
            | zero =>
              let A₀ := (KSingle (Round1State State U U τ) (U.erase x) (ks2 0) (defaultR1 U U τ)).mapInj
                (embedVert U U τ)
              have hA₀_C0 : A₀.C0 := by
                have h1 : 1 ≤ (U.erase x).card := by rw [Finset.card_erase_of_mem hxU]; omega
                obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
                exact SComplex.mapInj_C0 (embedVert_injective U U τ)
                  (single_cfg_C1 (r := 0) (initConfig (U.erase x) (defaultR1 U U τ))
                    ⟨i₀, defaultR1 U U τ i₀, by simp [initConfig, hi₀]⟩).1
              have eq_inter : (SComplex.sUnion (fun b => optFinLt b (some ⟨x, hxU⟩)) F₁).inter (P_W (U.erase x)) = A₀ := by
                ext s; simp only [SComplex.inter, SComplex.sUnion]
                constructor
                · rintro ⟨⟨b, hb, hsb⟩, hsx⟩
                  have hW1_union : ∀ W₁ : Finset (Fin n), (W₁ = U ∨ ∃ y ∈ U, y < x ∧ W₁ = U.erase y) →
                      U ⊆ W₁ ∪ U.erase x ∧ (P_W W₁).mem s → A₀.mem s := by
                    intro W₁ _ ⟨hUsub, hs1⟩
                    obtain ⟨τ_u, s_u, c_u, hs_ne, himg, rfl, hsc_u, _⟩ := inter_PW_extract hs1 hsx
                    have hcast : ((KAll (Round1State State U U τ) (U.erase x) (ks2 0)).mapInj (embedVert U U τ)).mem s :=
                      cast_KAll_mapInj hUsub ⟨s_u, ⟨hs_ne, initConfig (U.erase x) τ_u, ⟨τ_u, rfl⟩, hsc_u⟩, himg⟩
                    obtain ⟨s₀, ⟨hne₀, c₀, ⟨τ₀, rfl⟩, hsc₀⟩, himg₀⟩ := hcast
                    have hτ₀ : τ₀ = defaultR1 U U τ := funext (fun q => eq_defaultR1_of_U U τ q (τ₀ q))
                    subst hτ₀
                    exact ⟨s₀, ⟨hne₀, initConfig (U.erase x) (defaultR1 U U τ), rfl, hsc₀⟩, himg₀⟩
                  cases b with
                  | none =>
                    refine hW1_union U (Or.inl rfl) ⟨?_, hsb⟩
                    intro z hz; exact Finset.mem_union_left _ hz
                  | some y =>
                    have hyx : y.1 < x := hb
                    refine hW1_union (U.erase y.1) (Or.inr ⟨y.1, y.2, hyx, rfl⟩) ⟨?_, hsb⟩
                    intro z hzU
                    by_cases hzy : z = y.1
                    · subst hzy; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne_of_lt hyx, hzU⟩)
                    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzy, hzU⟩)
                · intro hsA
                  have hs_KAll : ((KAll (Round1State State U U τ) (U.erase x) (ks2 0)).mapInj (embedVert U U τ)).mem s :=
                    KSingle_le_KAll_mapInj hsA
                  refine ⟨⟨none, trivial, sub_KAll_zero_mapInj (Finset.erase_subset x U) hs_KAll⟩,
                    cast_KAll_mapInj (Finset.erase_subset x U) hs_KAll⟩
              rw [eq_inter]; exact hA₀_C0
            | succ r' =>
              let A₀ := (KSingle (Round1State State U U τ) (U.erase x) (ks12 r') (defaultR1 U U τ)).mapInj
                (embedVert U U τ)
              let Q₁ : Fin n → Prop := fun y => y ∈ U ∧ y < x
              let B₁ : Fin n → SComplex (Vert State (r' + 2)) := fun y =>
                (KSingle (Round1State State U U τ) ((U.erase x).erase y) (ks12 r') (defaultR1 U U τ)).mapInj
                  (embedVert U U τ)
              have hA₀_C0 : A₀.C0 := by
                have hcard1 : (∑ t, ks12 r' t) + 2 ≤ (U.erase x).card := by
                  rw [ks12_sum, Finset.card_erase_of_mem hxU]; omega
                exact SComplex.mapInj_C0 (embedVert_injective U U τ)
                  ((K_C0 (r' + 1) (Round1State State U U τ) (U.erase x) (ks12 r')
                    ks12_pos ks12_mono hcard1).1 (defaultR1 U U τ))
              have hB₁_C0 : ∀ y, Q₁ y → (B₁ y).C0 := by
                intro y ⟨hyU, hyx⟩
                have hy_mem : y ∈ U.erase x := Finset.mem_erase.mpr ⟨ne_of_lt hyx, hyU⟩
                have hcard2 : (∑ t, ks12 r' t) + 2 ≤ ((U.erase x).erase y).card := by
                  rw [ks12_sum, Finset.card_erase_of_mem hy_mem, Finset.card_erase_of_mem hxU]; omega
                exact SComplex.mapInj_C0 (embedVert_injective U U τ)
                  ((K_C0 (r' + 1) (Round1State State U U τ) ((U.erase x).erase y) (ks12 r')
                    ks12_pos ks12_mono hcard2).1 (defaultR1 U U τ))
              have hAB₁ : ∀ y, Q₁ y → (A₀.inter (B₁ y)).IsNonempty := by
                intro y ⟨hyU, hyx⟩
                let W_xy := (U.erase x).erase y
                have hy_mem : y ∈ U.erase x := Finset.mem_erase.mpr ⟨ne_of_lt hyx, hyU⟩
                have hWxy_pos : 1 ≤ W_xy.card := by
                  rw [Finset.card_erase_of_mem hy_mem, Finset.card_erase_of_mem hxU]; omega
                obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hWxy_pos
                have hdiff_le : (U.erase x \ W_xy).card ≤ ks12 r' 0 := by
                  have hsub : U.erase x \ W_xy ⊆ {y} := by
                    intro z hz; simp only [W_xy, Finset.mem_sdiff, Finset.mem_erase] at hz
                    simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
                  exact (Finset.card_le_card hsub).trans (by simp [ks12])
                refine ⟨embedVert U U τ ⟨i₀, cleanSubView W_xy (defaultR1 U U τ) (r' + 1) i₀⟩, ?_, ?_⟩
                · change A₀.vert _
                  rw [SComplex.mapInj_vert_iff (embedVert_injective U U τ)]
                  refine ⟨⟨i₀, cleanSubView W_xy (defaultR1 U U τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W_xy (defaultR1 U U τ) (r' + 1),
                      FIReach_silentCrash_cleanSubCfg (Finset.erase_subset y _) _ _ hdiff_le, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
                · change (B₁ y).vert _
                  rw [SComplex.mapInj_vert_iff (embedVert_injective U U τ)]
                  refine ⟨⟨i₀, cleanSubView W_xy (defaultR1 U U τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W_xy (defaultR1 U U τ) (r' + 1),
                      FIReach_cleanSubCfg W_xy (defaultR1 U U τ) (r' + 1) _, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
              have eq_inter : (SComplex.sUnion (fun b => optFinLt b (some ⟨x, hxU⟩)) F₁).inter (P_W (U.erase x)) =
                  A₀.union (SComplex.sUnion Q₁ B₁) := by
                ext s; simp only [SComplex.inter, SComplex.union, SComplex.sUnion]
                constructor
                · rintro ⟨⟨b, hb, hsb⟩, hsx⟩
                  cases b with
                  | none =>
                    obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                      inter_PW_extract hsx hsb
                    have hsubU : U ⊆ U.erase x ∪ U := fun z hz => Finset.mem_union_right _ hz
                    have h1 := strip1_mem_KSingle hxU hs_ne himg hreach_u hsc_u
                      (hnot_u x hxU (by simp))
                    have h2 := cast_KAll_mapInj hsubU (KSingle_le_KAll_mapInj h1)
                    obtain ⟨s₀, ⟨hne₀, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, himg₀⟩ := h2
                    have hτ₀ : τ₀ = defaultR1 U U τ := funext (fun q => eq_defaultR1_of_U U τ q (τ₀ q))
                    subst hτ₀
                    exact Or.inl ⟨s₀, ⟨hne₀, c₀, hreach₀, hsc₀⟩, himg₀⟩
                  | some y =>
                    have hyx : y.1 < x := hb
                    have hy_in : y.1 ∈ U.erase x := Finset.mem_erase.mpr ⟨ne_of_lt hyx, y.2⟩
                    obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                      inter_PW_extract hsb hsx
                    have hsubU : U ⊆ U.erase y.1 ∪ U.erase x := by
                      intro z hzU
                      by_cases hzy : z = y.1
                      · subst hzy; exact Finset.mem_union_right _ hy_in
                      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzy, hzU⟩)
                    have h1 := strip1_mem_KSingle hy_in hs_ne himg hreach_u hsc_u
                      (hnot_u y.1 hy_in (by simp))
                    have h2 := cast_KAll_mapInj hsubU (KSingle_le_KAll_mapInj h1)
                    obtain ⟨s₀, ⟨hne₀, c₀, ⟨τ₀, hreach₀⟩, hsc₀⟩, himg₀⟩ := h2
                    have hτ₀ : τ₀ = defaultR1 U U τ := funext (fun q => eq_defaultR1_of_U U τ q (τ₀ q))
                    subst hτ₀
                    exact Or.inr ⟨y.1, ⟨y.2, hyx⟩, s₀, ⟨hne₀, c₀, hreach₀, hsc₀⟩, himg₀⟩
                · rintro (hsA | ⟨y, ⟨hyU, hyx⟩, hsB⟩)
                  · have eq_ks2 : Fin.cons 2 (ks2 r') = ks2 (r' + 1) := by
                      funext t; cases t using Fin.cases <;> rfl
                    have hsU : (P_W U).mem s := by
                      have h := unstrip_KSingle_mapInj (k₀ := 2) (by omega) hxU hsA
                      rw [eq_ks2] at h
                      exact KSingle_le_KAll_mapInj h
                    have hsUx : (P_W (U.erase x)).mem s :=
                      cast_KAll_mapInj (Finset.erase_subset x U)
                        (mono_KAll_mapInj (fun t => by cases t using Fin.cases <;> simp [ks12, ks2])
                          (KSingle_le_KAll_mapInj hsA))
                    exact ⟨⟨none, trivial, hsU⟩, hsUx⟩
                  · have eq_ks2 : Fin.cons 2 (ks2 r') = ks2 (r' + 1) := by
                      funext t; cases t using Fin.cases <;> rfl
                    have hy_in : y ∈ U.erase x := Finset.mem_erase.mpr ⟨ne_of_lt hyx, hyU⟩
                    have hx_in : x ∈ U.erase y := Finset.mem_erase.mpr ⟨ne_of_gt hyx, hxU⟩
                    have hsUx : (P_W (U.erase x)).mem s := by
                      have h := unstrip_KSingle_mapInj (k₀ := 2) (by omega) hy_in hsB
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj (Finset.erase_subset x U) (KSingle_le_KAll_mapInj h)
                    have hsUy : (P_W (U.erase y)).mem s := by
                      have hsB' : ((KSingle (Round1State State U U τ) ((U.erase y).erase x) (ks12 r') (defaultR1 U U τ)).mapInj
                          (embedVert U U τ)).mem s := by
                        rwa [erase_comm_eq U y x]
                      have h := unstrip_KSingle_mapInj (k₀ := 2) (by omega) hx_in hsB'
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj (Finset.erase_subset y U) (KSingle_le_KAll_mapInj h)
                    exact ⟨⟨some ⟨y, hyU⟩, hyx, hsUy⟩, hsUx⟩
              rw [eq_inter]; exact SComplex.C0_star_union hA₀_C0 hB₁_C0 hAB₁
        -- Stage 2: glue PairIn U onto K₁
        let F₂ : Option (PairIn U) → SComplex (Vert State (r + 1)) :=
          fun | none => SComplex.sUnion (fun _ => True) F₁
              | some p => P_W ((U.erase p.1.1).erase p.1.2)
        refine SComplex.C1_sUnion_of_strictOrder optPairLt optPairLt_irrefl optPairLt_trans optPairLt_trich F₂
          (fun | none => hK₁_C1
               | some p => hPW_C1 ((U.erase p.1.1).erase p.1.2)
                   ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) (by
                     have hsub : U \ (U.erase p.1.1).erase p.1.2 ⊆ {p.1.1, p.1.2} := by
                       intro z hz
                       simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
                       by_contra h; push Not at h
                       exact hz.2 ⟨h.2, h.1, hz.1⟩
                     exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)))
          (fun a hex => ?_)
        cases a with
        | none => obtain ⟨b, hb⟩ := hex; cases b <;> simp [optPairLt] at hb
        | some p =>
          obtain ⟨⟨x, y⟩, hxU, hyU, hxy⟩ := p
          dsimp only [F₂]
          let W₂ := (U.erase x).erase y
          have hy_in_Ux : y ∈ U.erase x := Finset.mem_erase.mpr ⟨ne_of_gt hxy, hyU⟩
          have hx_in_Uy : x ∈ U.erase y := Finset.mem_erase.mpr ⟨ne_of_lt hxy, hxU⟩
          cases r with
          | zero =>
            let Jx := (KAll (Round1State State U (U.erase x) τ) W₂ (ks2 0)).mapInj (embedVert U (U.erase x) τ)
            let Jy := (KAll (Round1State State U (U.erase y) τ) W₂ (ks2 0)).mapInj (embedVert U (U.erase y) τ)
            have hW₂_card : (∑ t, ks2 0 t) + 2 ≤ W₂.card := by
              simp only [W₂, Finset.card_erase_of_mem hy_in_Ux, Finset.card_erase_of_mem hxU]
              simp; omega
            have hJx_C0 : Jx.C0 := SComplex.mapInj_C0 (embedVert_injective _ _ _)
              (K_C0 0 _ W₂ (ks2 0) (fun t => Fin.elim0 t) (fun t => Fin.elim0 t) hW₂_card).2
            have hJy_C0 : Jy.C0 := SComplex.mapInj_C0 (embedVert_injective _ _ _)
              (K_C0 0 _ W₂ (ks2 0) (fun t => Fin.elim0 t) (fun t => Fin.elim0 t) hW₂_card).2
            have hJxy_ne : (Jx.inter Jy).IsNonempty := by
              have h1 : 1 ≤ W₂.card := by omega
              obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
              refine ⟨⟨i₀, (τ i₀, initConfig U τ)⟩, ?_, ?_⟩
              · change Jx.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                refine ⟨⟨i₀, defaultR1 U (U.erase x) τ i₀⟩,
                  ⟨Finset.singleton_nonempty _, initConfig W₂ (defaultR1 U (U.erase x) τ),
                    ⟨defaultR1 U (U.erase x) τ, rfl⟩, ?_⟩, rfl⟩
                intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [initConfig, hi₀]
              · change Jy.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                refine ⟨⟨i₀, defaultR1 U (U.erase y) τ i₀⟩,
                  ⟨Finset.singleton_nonempty _, initConfig W₂ (defaultR1 U (U.erase y) τ),
                    ⟨defaultR1 U (U.erase y) τ, rfl⟩, ?_⟩, rfl⟩
                intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [initConfig, hi₀]
            have eq_inter : (SComplex.sUnion (fun b => optPairLt b (some ⟨(x, y), hxU, hyU, hxy⟩)) F₂).inter (P_W W₂) =
                Jx.union Jy := by
              ext s; simp only [SComplex.inter, SComplex.union, SComplex.sUnion]
              constructor
              · rintro ⟨⟨b, hb, hsb⟩, hs2⟩
                have from_W1 : ∀ W₁ : Finset (Fin n), W₁ ⊆ U → (x ∈ W₁ ∨ y ∈ W₁) → (P_W W₁).mem s →
                    Jx.mem s ∨ Jy.mem s := by
                  intro W₁ _ hxy_in hs1
                  obtain ⟨τ_u, s_u, c_u, hs_ne, himg, rfl, hsc_u, _⟩ := inter_PW_extract hs1 hs2
                  have hu : ((KAll (Round1State State U (W₁ ∪ W₂) τ) W₂ (ks2 0)).mapInj (embedVert U (W₁ ∪ W₂) τ)).mem s :=
                    ⟨s_u, ⟨hs_ne, initConfig W₂ τ_u, ⟨τ_u, rfl⟩, hsc_u⟩, himg⟩
                  rcases hxy_in with hxW₁ | hyW₁
                  · refine Or.inr (cast_KAll_mapInj ?_ hu)
                    intro z hz
                    obtain ⟨hzy, hzU⟩ := Finset.mem_erase.mp hz
                    by_cases hzx : z = x
                    · subst hzx; exact Finset.mem_union_left _ hxW₁
                    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzU⟩⟩)
                  · refine Or.inl (cast_KAll_mapInj ?_ hu)
                    intro z hz
                    obtain ⟨hzx, hzU⟩ := Finset.mem_erase.mp hz
                    by_cases hzy : z = y
                    · subst hzy; exact Finset.mem_union_left _ hyW₁
                    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzU⟩⟩)
                cases b with
                | none =>
                  obtain ⟨optX, _, hsb⟩ := hsb
                  cases optX with
                  | none => exact from_W1 U (Finset.Subset.refl U) (Or.inl hxU) hsb
                  | some z =>
                    by_cases hzx : z.1 = x
                    · exact from_W1 (U.erase z.1) (Finset.erase_subset _ _) (Or.inr (hzx ▸ hy_in_Ux)) hsb
                    · exact from_W1 (U.erase z.1) (Finset.erase_subset _ _) (Or.inl (Finset.mem_erase.mpr ⟨Ne.symm hzx, hxU⟩)) hsb
                | some q =>
                  obtain ⟨⟨u, v⟩, huU, hvU, huv⟩ := q
                  have hlt_q : u < x ∨ (u = x ∧ v < y) := hb
                  refine from_W1 ((U.erase u).erase v) ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) ?_ hsb
                  rcases hlt_q with hux | ⟨rfl, hvy⟩
                  · by_cases hvx : v = x
                    · subst hvx
                      exact Or.inr (Finset.mem_erase.mpr ⟨ne_of_gt hxy, Finset.mem_erase.mpr ⟨ne_of_gt (lt_trans hux hxy), hyU⟩⟩)
                    · exact Or.inl (Finset.mem_erase.mpr ⟨Ne.symm hvx, Finset.mem_erase.mpr ⟨ne_of_gt hux, hxU⟩⟩)
                  · exact Or.inr (Finset.mem_erase.mpr ⟨ne_of_gt hvy, Finset.mem_erase.mpr ⟨ne_of_gt hxy, hyU⟩⟩)
              · rintro (hsJx | hsJy)
                · refine ⟨⟨none, trivial, some ⟨x, hxU⟩, trivial,
                    sub_KAll_zero_mapInj (Finset.erase_subset y (U.erase x)) hsJx⟩,
                    cast_KAll_mapInj (Finset.erase_subset y (U.erase x)) hsJx⟩
                · have hsub_y : W₂ ⊆ U.erase y := by
                    dsimp only [W₂]; rw [erase_comm_eq U x y]; exact Finset.erase_subset x (U.erase y)
                  refine ⟨⟨none, trivial, some ⟨y, hyU⟩, trivial, sub_KAll_zero_mapInj hsub_y hsJy⟩,
                    cast_KAll_mapInj hsub_y hsJy⟩
            rw [eq_inter]; exact SComplex.C0_union hJx_C0 hJy_C0 hJxy_ne
          | succ r' =>
            let Jx := (KAll (Round1State State U (U.erase x) τ) W₂ (ks12 r')).mapInj (embedVert U (U.erase x) τ)
            let Jy := (KAll (Round1State State U (U.erase y) τ) W₂ (ks12 r')).mapInj (embedVert U (U.erase y) τ)
            let A₀ := Jx.union Jy
            -- Extra branches: (0, u) for K_ux (u < x), (1, u) for K_uy (u < x), (2, v) for K_xv (x < v < y)
            let Q₂ : Fin 3 × Fin n → Prop := fun kw =>
              (kw.1 = 0 ∧ kw.2 ∈ U ∧ kw.2 < x) ∨
              (kw.1 = 1 ∧ kw.2 ∈ U ∧ kw.2 < x) ∨
              (kw.1 = 2 ∧ kw.2 ∈ U ∧ x < kw.2 ∧ kw.2 < y)
            let B₂ : Fin 3 × Fin n → SComplex (Vert State (r' + 2)) := fun kw =>
              if kw.1 = 1 then
                (KAll (Round1State State U (U.erase y) τ) (W₂.erase kw.2) (ks12 r')).mapInj (embedVert U (U.erase y) τ)
              else
                (KAll (Round1State State U (U.erase x) τ) (W₂.erase kw.2) (ks12 r')).mapInj (embedVert U (U.erase x) τ)
            have hW₂_card : (∑ t, ks12 r' t) + 2 ≤ W₂.card := by
              rw [ks12_sum, Finset.card_erase_of_mem hy_in_Ux, Finset.card_erase_of_mem hxU]; omega
            have hJx_C0 : Jx.C0 := SComplex.mapInj_C0 (embedVert_injective _ _ _)
              (K_C0 (r' + 1) _ W₂ (ks12 r') ks12_pos ks12_mono hW₂_card).2
            have hJy_C0 : Jy.C0 := SComplex.mapInj_C0 (embedVert_injective _ _ _)
              (K_C0 (r' + 1) _ W₂ (ks12 r') ks12_pos ks12_mono hW₂_card).2
            have hA₀_C0 : A₀.C0 := by
              refine SComplex.C0_union hJx_C0 hJy_C0 ?_
              have h1 : 1 ≤ W₂.card := by omega
              obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
              have h_emb : ∀ {m : ℕ} (j : Fin n),
                  embedView U (U.erase x) τ j (cleanSubView W₂ (defaultR1 U (U.erase x) τ) m j) =
                  embedView U (U.erase y) τ j (cleanSubView W₂ (defaultR1 U (U.erase y) τ) m j) := by
                intro m; induction m with
                | zero => intro j; rfl
                | succ m ihm =>
                  intro j; simp only [cleanSubView, embedView]
                  refine Prod.ext (ihm j) ?_; funext l; by_cases hl : l ∈ W₂ <;> simp [hl, ihm l]
              refine ⟨embedVert U (U.erase y) τ ⟨i₀, cleanSubView W₂ (defaultR1 U (U.erase y) τ) (r' + 1) i₀⟩, ?_, ?_⟩
              · change Jx.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                refine ⟨⟨i₀, cleanSubView W₂ (defaultR1 U (U.erase x) τ) (r' + 1) i₀⟩,
                  ⟨Finset.singleton_nonempty _, cleanSubCfg W₂ (defaultR1 U (U.erase x) τ) (r' + 1),
                    ⟨defaultR1 U (U.erase x) τ, FIReach_cleanSubCfg W₂ _ _ _⟩, ?_⟩,
                  Sigma.ext rfl (heq_of_eq (h_emb i₀))⟩
                intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
              · change Jy.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                refine ⟨⟨i₀, cleanSubView W₂ (defaultR1 U (U.erase y) τ) (r' + 1) i₀⟩,
                  ⟨Finset.singleton_nonempty _, cleanSubCfg W₂ (defaultR1 U (U.erase y) τ) (r' + 1),
                    ⟨defaultR1 U (U.erase y) τ, FIReach_cleanSubCfg W₂ _ _ _⟩, ?_⟩, rfl⟩
                intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
            have hw_in_W₂ : ∀ kw, Q₂ kw → kw.2 ∈ W₂ := by
              rintro ⟨k, w⟩ (⟨_, hwU, hwx⟩ | ⟨_, hwU, hwx⟩ | ⟨_, hwU, hxw, hwy⟩)
              · exact Finset.mem_erase.mpr ⟨ne_of_lt (lt_trans hwx hxy), Finset.mem_erase.mpr ⟨ne_of_lt hwx, hwU⟩⟩
              · exact Finset.mem_erase.mpr ⟨ne_of_lt (lt_trans hwx hxy), Finset.mem_erase.mpr ⟨ne_of_lt hwx, hwU⟩⟩
              · exact Finset.mem_erase.mpr ⟨ne_of_lt hwy, Finset.mem_erase.mpr ⟨ne_of_gt hxw, hwU⟩⟩
            have hB₂_C0 : ∀ kw, Q₂ kw → (B₂ kw).C0 := by
              intro kw hkw
              have hwW₂ := hw_in_W₂ kw hkw
              have hcard_w : (∑ t, ks12 r' t) + 2 ≤ (W₂.erase kw.2).card := by
                rw [ks12_sum, Finset.card_erase_of_mem hwW₂, Finset.card_erase_of_mem hy_in_Ux, Finset.card_erase_of_mem hxU]
                omega
              dsimp only [B₂]
              split_ifs
              · exact SComplex.mapInj_C0 (embedVert_injective _ _ _)
                  (K_C0 (r' + 1) _ (W₂.erase kw.2) (ks12 r') ks12_pos ks12_mono hcard_w).2
              · exact SComplex.mapInj_C0 (embedVert_injective _ _ _)
                  (K_C0 (r' + 1) _ (W₂.erase kw.2) (ks12 r') ks12_pos ks12_mono hcard_w).2
            have hAB₂ : ∀ kw, Q₂ kw → (A₀.inter (B₂ kw)).IsNonempty := by
              intro kw hkw
              have hwW₂ := hw_in_W₂ kw hkw
              let W₃ := W₂.erase kw.2
              have h1 : 1 ≤ W₃.card := by
                rw [Finset.card_erase_of_mem hwW₂, Finset.card_erase_of_mem hy_in_Ux, Finset.card_erase_of_mem hxU]; omega
              obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp h1
              have hdiff_le : (W₂ \ W₃).card ≤ ks12 r' 0 := by
                have hsub : W₂ \ W₃ ⊆ {kw.2} := by
                  intro z hz; simp only [W₃, Finset.mem_sdiff, Finset.mem_erase] at hz
                  simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
                exact (Finset.card_le_card hsub).trans (by simp [ks12])
              dsimp only [B₂]
              split_ifs with hk1
              · refine ⟨embedVert U (U.erase y) τ ⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase y) τ) (r' + 1) i₀⟩,
                  Or.inr ?_, ?_⟩
                · change Jy.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                  refine ⟨⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase y) τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W₃ (defaultR1 U (U.erase y) τ) (r' + 1),
                      ⟨defaultR1 U (U.erase y) τ, FIReach_silentCrash_cleanSubCfg (Finset.erase_subset _ _) _ _ hdiff_le⟩, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
                · change ((KAll (Round1State State U (U.erase y) τ) (W₂.erase kw.2) (ks12 r')).mapInj
                    (embedVert U (U.erase y) τ)).vert _
                  rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                  refine ⟨⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase y) τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W₃ (defaultR1 U (U.erase y) τ) (r' + 1),
                      ⟨defaultR1 U (U.erase y) τ, FIReach_cleanSubCfg W₃ _ _ _⟩, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
              · refine ⟨embedVert U (U.erase x) τ ⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase x) τ) (r' + 1) i₀⟩,
                  Or.inl ?_, ?_⟩
                · change Jx.vert _; rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                  refine ⟨⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase x) τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W₃ (defaultR1 U (U.erase x) τ) (r' + 1),
                      ⟨defaultR1 U (U.erase x) τ, FIReach_silentCrash_cleanSubCfg (Finset.erase_subset _ _) _ _ hdiff_le⟩, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
                · change ((KAll (Round1State State U (U.erase x) τ) (W₂.erase kw.2) (ks12 r')).mapInj
                    (embedVert U (U.erase x) τ)).vert _
                  rw [SComplex.mapInj_vert_iff (embedVert_injective _ _ _)]
                  refine ⟨⟨i₀, cleanSubView W₃ (defaultR1 U (U.erase x) τ) (r' + 1) i₀⟩,
                    ⟨Finset.singleton_nonempty _, cleanSubCfg W₃ (defaultR1 U (U.erase x) τ) (r' + 1),
                      ⟨defaultR1 U (U.erase x) τ, FIReach_cleanSubCfg W₃ _ _ _⟩, ?_⟩, rfl⟩
                  intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hi₀]
            have eq_inter : (SComplex.sUnion (fun b => optPairLt b (some ⟨(x, y), hxU, hyU, hxy⟩)) F₂).inter (P_W W₂) =
                A₀.union (SComplex.sUnion Q₂ B₂) := by
              have eq_ks2 : Fin.cons 2 (ks2 r') = ks2 (r' + 1) := by
                funext t; cases t using Fin.cases <;> rfl
              ext s; simp only [SComplex.inter, SComplex.union, SComplex.sUnion]
              constructor
              · rintro ⟨⟨b, hb, hsb⟩, hs2⟩
                cases b with
                | none =>
                  obtain ⟨optX, _, hsb⟩ := hsb
                  cases optX with
                  | none =>
                    obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                      inter_PW_extract hs2 hsb
                    have h1 := strip2_mem_KSingle hxU hy_in_Ux hs_ne himg hreach_u hsc_u
                      (hnot_u x hxU (by simp [W₂]))
                      (hnot_u y hyU (by simp [W₂]))
                    have h2 := mono_KAll_mapInj
                      (ks₂ := ks12 r') (fun t => by cases t using Fin.cases <;> simp [ks12, ks2])
                      (KSingle_le_KAll_mapInj h1)
                    exact Or.inl (Or.inl (cast_KAll_mapInj (by intro a ha; exact Finset.mem_union_right _ (Finset.erase_subset x U ha)) h2))
                  | some z =>
                    by_cases hzx : z.1 = x
                    · subst hzx
                      obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                        inter_PW_extract hs2 hsb
                      have h1 := strip1_mem_KSingle hy_in_Ux hs_ne himg hreach_u hsc_u
                        (hnot_u y hy_in_Ux (by simp [W₂]))
                      exact Or.inl (Or.inl (cast_KAll_mapInj (fun a ha => Finset.mem_union_right _ ha)
                        (KSingle_le_KAll_mapInj h1)))
                    · by_cases hzy : z.1 = y
                      · subst hzy
                        obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                          inter_PW_extract hs2 hsb
                        have h1 := strip1_mem_KSingle hx_in_Uy hs_ne himg hreach_u hsc_u
                          (hnot_u x hx_in_Uy (by simp [W₂]))
                        have h1' : ((KAll (Round1State State U (W₂ ∪ U.erase z.1) τ) W₂ (ks12 r')).mapInj
                            (embedVert U (W₂ ∪ U.erase z.1) τ)).mem s := by
                          have h1k := KSingle_le_KAll_mapInj h1
                          rwa [← show W₂ = (U.erase z.1).erase x from erase_comm_eq U x z.1] at h1k
                        exact Or.inl (Or.inr (cast_KAll_mapInj (fun a ha => Finset.mem_union_right _ ha) h1'))
                      · -- z ∉ {x, y}: strip x, y from U.erase z, then unstrip z onto W₂!
                        obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                          inter_PW_extract hs2 hsb
                        have hx_in_Uz : x ∈ U.erase z.1 := Finset.mem_erase.mpr ⟨Ne.symm hzx, hxU⟩
                        have hy_in_Uxz : y ∈ (U.erase z.1).erase x :=
                          Finset.mem_erase.mpr ⟨ne_of_gt hxy, Finset.mem_erase.mpr ⟨Ne.symm hzy, hyU⟩⟩
                        have hz_in_W₂ : z.1 ∈ W₂ :=
                          Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, z.2⟩⟩
                        have h1 := strip2_mem_KSingle hx_in_Uz hy_in_Uxz hs_ne himg hreach_u hsc_u
                          (hnot_u x hx_in_Uz (by simp [W₂]))
                          (hnot_u y (Finset.mem_erase.mpr ⟨Ne.symm hzy, hyU⟩) (by simp [W₂]))
                        have heq_set : ((U.erase z.1).erase x).erase y = W₂.erase z.1 := by
                          ext a; simp only [W₂, Finset.mem_erase]; tauto
                        have h2 : ((KAll (Round1State State U (W₂ ∪ U.erase z.1) τ) (W₂.erase z.1)
                            (Fin.cons 0 (ks2 r'))).mapInj (embedVert U (W₂ ∪ U.erase z.1) τ)).mem s := by
                          rw [← heq_set]; exact KSingle_le_KAll_mapInj h1
                        have h3 := unstrip_KAll_mapInj (k₀ := 1) (by omega) hz_in_W₂ h2
                        refine Or.inl (Or.inl (cast_KAll_mapInj ?_ h3))
                        intro a ha
                        by_cases haz : a = z.1
                        · subst haz; exact Finset.mem_union_left _ hz_in_W₂
                        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨haz, Finset.mem_of_mem_erase ha⟩)
                | some q =>
                  obtain ⟨⟨u, v⟩, huU, hvU, huv⟩ := q
                  have hlt_q : u < x ∨ (u = x ∧ v < y) := hb
                  -- Keep W₂ as second argument so c_u starts on W₂!
                  obtain ⟨τ_u, s_u, c_u, hs_ne, himg, hreach_u, hsc_u, hnot_u⟩ :=
                    inter_PW_extract hsb hs2
                  rcases hlt_q with hux | ⟨rfl, hvy⟩
                  · have hu_in_W₂ : u ∈ W₂ :=
                      Finset.mem_erase.mpr ⟨ne_of_lt (lt_trans hux hxy), Finset.mem_erase.mpr ⟨ne_of_lt hux, huU⟩⟩
                    by_cases hvx : v = x
                    · subst hvx
                      have h1 := strip1_mem_KSingle hu_in_W₂ hs_ne himg hreach_u hsc_u
                        (hnot_u u hu_in_W₂ (by simp))
                      refine Or.inr ⟨(0, u), Or.inl ⟨rfl, huU, hux⟩, ?_⟩
                      dsimp only [B₂]; rw [if_neg (by decide : (0 : Fin 3) ≠ 1)]
                      refine cast_KAll_mapInj ?_ (KSingle_le_KAll_mapInj h1)
                      intro a ha
                      obtain ⟨hax, haU⟩ := Finset.mem_erase.mp ha
                      by_cases hay : a = y
                      · subst hay
                        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_gt hxy, Finset.mem_erase.mpr ⟨ne_of_gt (lt_trans hux hxy), hyU⟩⟩)
                      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, haU⟩⟩)
                    · by_cases hvy : v = y
                      · subst hvy
                        have h1 := strip1_mem_KSingle hu_in_W₂ hs_ne himg hreach_u hsc_u
                          (hnot_u u hu_in_W₂ (by simp))
                        refine Or.inr ⟨(1, u), Or.inr (Or.inl ⟨rfl, huU, hux⟩), ?_⟩
                        dsimp only [B₂]; rw [if_pos rfl]
                        refine cast_KAll_mapInj ?_ (KSingle_le_KAll_mapInj h1)
                        intro a ha
                        obtain ⟨hay, haU⟩ := Finset.mem_erase.mp ha
                        by_cases hax : a = x
                        · subst hax
                          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_lt hxy, Finset.mem_erase.mpr ⟨ne_of_gt hux, hxU⟩⟩)
                        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, haU⟩⟩)
                      · -- v ∉ {x, y}: strip u and v from W₂, then unstrip v onto W₂.erase u!
                        have hv_in_W₂u : v ∈ W₂.erase u :=
                          Finset.mem_erase.mpr ⟨ne_of_gt huv, Finset.mem_erase.mpr ⟨hvy, Finset.mem_erase.mpr ⟨hvx, hvU⟩⟩⟩
                        have hv_in_W₂ : v ∈ W₂ := Finset.mem_of_mem_erase hv_in_W₂u
                        have h1 := strip2_mem_KSingle hu_in_W₂ hv_in_W₂u hs_ne himg hreach_u hsc_u
                          (hnot_u u hu_in_W₂ (by simp))
                          (hnot_u v hv_in_W₂ (by simp))
                        have h2 := unstrip_KAll_mapInj (k₀ := 1) (by omega) hv_in_W₂u (KSingle_le_KAll_mapInj h1)
                        refine Or.inr ⟨(0, u), Or.inl ⟨rfl, huU, hux⟩, ?_⟩
                        dsimp only [B₂]; rw [if_neg (by decide : (0 : Fin 3) ≠ 1)]
                        refine cast_KAll_mapInj ?_ h2
                        intro a ha
                        obtain ⟨hax, haU⟩ := Finset.mem_erase.mp ha
                        by_cases hay : a = y
                        · subst hay
                          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Ne.symm hvy, Finset.mem_erase.mpr ⟨ne_of_gt (lt_trans hux hxy), hyU⟩⟩)
                        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, haU⟩⟩)
                  · -- u = x and x < v < y: strip v from W₂!
                    have hv_in_W₂ : v ∈ W₂ :=
                      Finset.mem_erase.mpr ⟨ne_of_lt hvy, Finset.mem_erase.mpr ⟨ne_of_gt huv, hvU⟩⟩
                    have h1 := strip1_mem_KSingle hv_in_W₂ hs_ne himg hreach_u hsc_u
                      (hnot_u v hv_in_W₂ (by simp))
                    refine Or.inr ⟨(2, v), Or.inr (Or.inr ⟨rfl, hvU, huv, hvy⟩), ?_⟩
                    dsimp only [B₂]; rw [if_neg (by decide : (2 : Fin 3) ≠ 1)]
                    refine cast_KAll_mapInj ?_ (KSingle_le_KAll_mapInj h1)
                    intro a ha
                    obtain ⟨hax, haU⟩ := Finset.mem_erase.mp ha
                    by_cases hay : a = y
                    · subst hay
                      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_gt hvy, Finset.mem_erase.mpr ⟨ne_of_gt hxy, hyU⟩⟩)
                    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, haU⟩⟩)
              · -- Reverse direction: A₀ ∪ ⋃ B₂ ⊆ (sUnion ... F₂) ∩ P_W W₂
                rintro ((hsJx | hsJy) | ⟨⟨k, w⟩, hQ, hsB⟩)
                · have hsUx : (P_W (U.erase x)).mem s := by
                    have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hy_in_Ux hsJx
                    rwa [eq_ks2] at h
                  have hsW₂ : (P_W W₂).mem s :=
                    cast_KAll_mapInj (Finset.erase_subset y (U.erase x))
                      (mono_KAll_mapInj (fun t => by cases t using Fin.cases <;> simp [ks12, ks2]) hsJx)
                  exact ⟨⟨none, trivial, some ⟨x, hxU⟩, trivial, hsUx⟩, hsW₂⟩
                · have hsUy : (P_W (U.erase y)).mem s := by
                    have hsJy' : ((KAll (Round1State State U (U.erase y) τ) ((U.erase y).erase x) (ks12 r')).mapInj
                        (embedVert U (U.erase y) τ)).mem s := by
                      dsimp only [Jy, W₂] at hsJy
                      rwa [erase_comm_eq U y x]
                    have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hx_in_Uy hsJy'
                    rwa [eq_ks2] at h
                  have hsub_y : W₂ ⊆ U.erase y := by
                    dsimp only [W₂]; rw [erase_comm_eq U x y]; exact Finset.erase_subset x (U.erase y)
                  have hsW₂ : (P_W W₂).mem s :=
                    cast_KAll_mapInj hsub_y
                      (mono_KAll_mapInj (fun t => by cases t using Fin.cases <;> simp [ks12, ks2]) hsJy)
                  exact ⟨⟨none, trivial, some ⟨y, hyU⟩, trivial, hsUy⟩, hsW₂⟩
                · rcases hQ with ⟨hk0, hwU, hwx⟩ | ⟨hk1, hwU, hwx⟩ | ⟨hk2, hwU, hxw, hwy⟩
                  · subst hk0
                    dsimp only [B₂] at hsB
                    rw [if_neg (by decide : (0 : Fin 3) ≠ 1)] at hsB
                    have hw_in_W₂ : w ∈ W₂ :=
                      Finset.mem_erase.mpr ⟨ne_of_lt (lt_trans hwx hxy), Finset.mem_erase.mpr ⟨ne_of_lt hwx, hwU⟩⟩
                    have hy_in_Uwx : y ∈ (U.erase w).erase x :=
                      Finset.mem_erase.mpr ⟨ne_of_gt hxy, Finset.mem_erase.mpr ⟨ne_of_gt (lt_trans hwx hxy), hyU⟩⟩
                    have h_set : W₂.erase w = ((U.erase w).erase x).erase y := by
                      ext a; simp only [W₂, Finset.mem_erase]; tauto
                    have hsW₂ : (P_W W₂).mem s := by
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hw_in_W₂ hsB
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj (Finset.erase_subset y (U.erase x)) h
                    have hsUwx : (P_W ((U.erase w).erase x)).mem s := by
                      have hsB' := hsB
                      rw [h_set] at hsB'
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hy_in_Uwx hsB'
                      rw [eq_ks2] at h
                      refine cast_KAll_mapInj ?_ h
                      rw [erase_comm_eq U w x]; exact Finset.erase_subset w (U.erase x)
                    exact ⟨⟨some ⟨(w, x), hwU, hxU, hwx⟩, Or.inl hwx, hsUwx⟩, hsW₂⟩
                  · subst hk1
                    dsimp only [B₂] at hsB
                    rw [if_pos rfl] at hsB
                    have hw_in_W₂ : w ∈ W₂ :=
                      Finset.mem_erase.mpr ⟨ne_of_lt (lt_trans hwx hxy), Finset.mem_erase.mpr ⟨ne_of_lt hwx, hwU⟩⟩
                    have hx_in_Uwy : x ∈ (U.erase w).erase y :=
                      Finset.mem_erase.mpr ⟨ne_of_lt hxy, Finset.mem_erase.mpr ⟨ne_of_gt hwx, hxU⟩⟩
                    have h_set : W₂.erase w = ((U.erase w).erase y).erase x := by
                      ext a; simp only [W₂, Finset.mem_erase]; tauto
                    have hsub_y : W₂ ⊆ U.erase y := by
                      dsimp only [W₂]; rw [erase_comm_eq U x y]; exact Finset.erase_subset x (U.erase y)
                    have hsW₂ : (P_W W₂).mem s := by
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hw_in_W₂ hsB
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj hsub_y h
                    have hsUwy : (P_W ((U.erase w).erase y)).mem s := by
                      have hsB' := hsB
                      rw [h_set] at hsB'
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hx_in_Uwy hsB'
                      rw [eq_ks2] at h
                      refine cast_KAll_mapInj ?_ h
                      rw [erase_comm_eq U w y]; exact Finset.erase_subset w (U.erase y)
                    exact ⟨⟨some ⟨(w, y), hwU, hyU, lt_trans hwx hxy⟩, Or.inl hwx, hsUwy⟩, hsW₂⟩
                  · subst hk2
                    dsimp only [B₂] at hsB
                    rw [if_neg (by decide : (2 : Fin 3) ≠ 1)] at hsB
                    have hw_in_W₂ : w ∈ W₂ :=
                      Finset.mem_erase.mpr ⟨ne_of_lt hwy, Finset.mem_erase.mpr ⟨ne_of_gt hxw, hwU⟩⟩
                    have hy_in_Uxw : y ∈ (U.erase x).erase w :=
                      Finset.mem_erase.mpr ⟨ne_of_gt hwy, hy_in_Ux⟩
                    have h_set : W₂.erase w = ((U.erase x).erase w).erase y :=
                      erase_comm_eq (U.erase x) y w
                    have hsW₂ : (P_W W₂).mem s := by
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hw_in_W₂ hsB
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj (Finset.erase_subset y (U.erase x)) h
                    have hsUxw : (P_W ((U.erase x).erase w)).mem s := by
                      have hsB' := hsB
                      rw [h_set] at hsB'
                      have h := unstrip_KAll_mapInj (k₀ := 2) (by omega) hy_in_Uxw hsB'
                      rw [eq_ks2] at h
                      exact cast_KAll_mapInj (Finset.erase_subset w (U.erase x)) h
                    exact ⟨⟨some ⟨(x, w), hxU, hwU, hxw⟩, Or.inr ⟨rfl, hwy⟩, hsUxw⟩, hsW₂⟩
            rw [eq_inter]; exact SComplex.C0_star_union hA₀_C0 hB₂_C0 hAB₂
      -- Finally: KAll_C1 at r + 1
      refine ⟨hSingle, ?_⟩
      rw [KAll_eq_sUnion_InitCfg]
      refine SComplex.C1_sUnion_of_strictOrder cfgLt cfgLt_irrefl cfgLt_trans cfgLt_trich _
        (fun τ => hSingle τ.1) (fun τ ⟨σ, hστ⟩ => ?_)
      rw [KAll_inter_lt_eq_succ]
      obtain ⟨p₀, _, hlt₀⟩ := hστ
      have hp₀U : p₀ ∈ U := by
        by_contra h; rw [σ.2 p₀ h, τ.2 p₀ h] at hlt₀; exact Nat.lt_irrefl _ hlt₀
      let P_idx : Fin n → Prop := fun p => p ∈ U ∧ ∃ s₀ : State p, stateRank State p s₀ < stateRank State p (τ.1 p)
      let B_p : Fin n → SComplex (Vert State (r + 1)) := fun p => KSingle State (U.erase p) (ks12 r) τ.1
      have hp₀ : P_idx p₀ := ⟨hp₀U, σ.1 p₀, hlt₀⟩
      have eq_u : SComplex.sUnion P_idx B_p = (B_p p₀).union (SComplex.sUnion P_idx B_p) := by
        ext s; simp only [SComplex.sUnion, SComplex.union]
        exact ⟨Or.inr, fun h => h.elim (fun hs => ⟨p₀, hp₀, hs⟩) id⟩
      rw [eq_u]
      have hBp_C0 : ∀ p, P_idx p → (B_p p).C0 := by
        intro p ⟨hpU, _⟩
        have hcard1 : (∑ t, ks12 r t) + 2 ≤ (U.erase p).card := by
          rw [ks12_sum, Finset.card_erase_of_mem hpU]; omega
        exact (K_C0 (r + 1) State (U.erase p) (ks12 r) ks12_pos ks12_mono hcard1).1 τ.1
      refine SComplex.C0_star_union (hBp_C0 p₀ hp₀) hBp_C0 (fun p ⟨hpU, _⟩ => ?_)
      let W_pp := (U.erase p₀).erase p
      have hWpp_pos : 1 ≤ W_pp.card := by
        have h1 : (U.erase p₀).card = U.card - 1 := Finset.card_erase_of_mem hp₀U
        have h2 : (U.erase p₀).card - 1 ≤ W_pp.card := Finset.pred_card_le_card_erase
        omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hWpp_pos
      have hdiff1 : (U.erase p₀ \ W_pp).card ≤ ks12 r 0 := by
        have hsub : U.erase p₀ \ W_pp ⊆ {p} := by
          intro z hz; simp only [W_pp, Finset.mem_sdiff, Finset.mem_erase] at hz
          simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
        exact (Finset.card_le_card hsub).trans (by simp [ks12])
      have hdiff2 : (U.erase p \ W_pp).card ≤ ks12 r 0 := by
        have hsub : U.erase p \ W_pp ⊆ {p₀} := by
          intro z hz; dsimp only [W_pp] at hz; rw [erase_comm_eq U p₀ p] at hz
          simp only [Finset.mem_sdiff, Finset.mem_erase] at hz
          simp [Classical.not_not.mp fun h => hz.2 ⟨h, hz.1⟩]
        exact (Finset.card_le_card hsub).trans (by simp [ks12])
      have hWpp2 : W_pp ⊆ U.erase p := by
        dsimp only [W_pp]; rw [erase_comm_eq U p₀ p]; exact Finset.erase_subset p₀ (U.erase p)
      refine ⟨⟨q, cleanSubView W_pp τ.1 (r + 1) q⟩,
        ⟨Finset.singleton_nonempty _, cleanSubCfg W_pp τ.1 (r + 1),
          FIReach_silentCrash_cleanSubCfg (Finset.erase_subset p (U.erase p₀)) τ.1 _ hdiff1, ?_⟩,
        ⟨Finset.singleton_nonempty _, cleanSubCfg W_pp τ.1 (r + 1),
          FIReach_silentCrash_cleanSubCfg hWpp2 τ.1 _ hdiff2, ?_⟩⟩
      · intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hq]
      · intro z hz; rcases Finset.mem_singleton.mp hz with rfl; simp [cleanSubCfg, hq]

/-! ### Part 3: Non-trivial Counting Lower Bound (Section 6 / Theorem 6) -/

def evalState {n : ℕ} {O : Type} (P : Protocol n O) :
    {r : ℕ} → (i : Fin n) → View P.State r i → P.State i
  | 0, _, s => s
  | _ + 1, i, (_, M) => P.transition i (fun j => (M j).map (evalState P j))

def outVert {n : ℕ} {O : Type} (P : Protocol n O) (r : ℕ) (x : Vert P.State r) : O :=
  P.output x.1 (evalState P x.1 x.2)

def prefixVert {n : ℕ} {O : Type} (P : Protocol n O) (r : ℕ)
    (y : Vert P.State (r + 1)) : Vert P.State r :=
  ⟨y.1, y.2.1⟩

def suffixView {n : ℕ} {O : Type} (P : Protocol n O) :
    {r : ℕ} → (i : Fin n) → View P.State (r + 1) i → View P.State r i
  | 0, i, (_, M) => P.transition i M
  | _ + 1, i, (v, M) => (suffixView P i v, fun j => (M j).map (suffixView P j))

def suffixVert {n : ℕ} {O : Type} (P : Protocol n O) (r : ℕ)
    (y : Vert P.State (r + 1)) : Vert P.State r :=
  ⟨y.1, suffixView P y.1 y.2⟩

lemma suffixView_embedView {n : ℕ} {O : Type} (P : Protocol n O)
    (U W : Finset (Fin n)) (τ : (i : Fin n) → P.State i) :
    ∀ {r : ℕ} (i : Fin n) (v' : View (Round1State P.State U W τ) r i),
      suffixView P i (embedView U W τ i v') =
      mapView (fun j m => P.transition j m.val) i v'
  | 0, _, _ => rfl
  | _ + 1, i, (v, M) => by
      dsimp only [embedView, suffixView, mapView]
      refine Prod.ext (suffixView_embedView P U W τ i v) ?_
      funext j
      dsimp only
      cases M j with
      | none => rfl
      | some w => exact congrArg some (suffixView_embedView P U W τ j w)

/-- Lemma 12(a), prefix configuration witness. -/
lemma prefixCfg_exists {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {τ : (i : Fin n) → P.State i}
    {c : (i : Fin n) → Option (View P.State (T' + 1) i)}
    (hreach : FIReach (T' + 1) (fun _ : Fin (T' + 1) => 1) (initConfig Finset.univ τ) c) :
    ∃ τ' d, FIReach T' (ks2 T') (initConfig Finset.univ τ') d ∧
      ∀ i vm, c i = some vm → d i = some vm.1 := by
  obtain ⟨b, hb, _, hstep⟩ := hreach
  exact ⟨τ, b, FIReach_mono (fun _ => by simp [ks2]) hb, fun i vm hci => (hstep i vm hci).1⟩

/-- Lemma 12(a), suffix configuration witness. -/
lemma suffixCfg_exists {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {τ : (i : Fin n) → P.State i}
    {c : (i : Fin n) → Option (View P.State (T' + 1) i)}
    (hreach : FIReach (T' + 1) (fun _ : Fin (T' + 1) => 1) (initConfig Finset.univ τ) c) :
    ∃ τ' d, FIReach T' (ks2 T') (initConfig Finset.univ τ') d ∧
      ∀ i vm, c i = some vm → d i = some (suffixView P i vm) := by
  obtain ⟨W, _, hWcard, τ₁, c', hreach', hceq⟩ :=
    (FIReach_succ_iff Finset.univ τ (fun _ : Fin (T' + 1) => 1) c).mp hreach
  obtain ⟨τ', hτ'⟩ : ∃ τ' : (i : Fin n) → P.State i,
      τ' = fun j => P.transition j (τ₁ j).val := ⟨_, rfl⟩
  have hmap := mapView_FIReach
    (fun j (m : Round1State P.State Finset.univ W τ j) => P.transition j m.val) hreach'
  rw [← hτ'] at hmap
  have hcfg_eq : (fun i => (c' i).map (mapView (fun j m => P.transition j m.val) i)) =
      (fun i => (c i).map (suffixView P i)) := by
    funext i
    rw [hceq i]
    cases c' i with
    | none => rfl
    | some v' => exact congrArg some (suffixView_embedView P Finset.univ W τ i v').symm
  rw [hcfg_eq] at hmap
  cases T' with
  | zero =>
    change (fun i => (c i).map (suffixView P i)) = initConfig W τ' at hmap
    refine ⟨τ', initConfig Finset.univ τ', rfl, fun i vm hci => ?_⟩
    have hcy : (c i).map (suffixView P i) = some (suffixView P i vm) := by simp [hci]
    have hwi : initConfig W τ' i = some (suffixView P i vm) :=
      (congr_fun hmap i).symm.trans hcy
    simp only [initConfig] at hwi ⊢
    split_ifs at hwi with hiW
    simp only [Option.some.injEq] at hwi
    simp [hwi]
  | succ r =>
    refine ⟨τ', fun i => (c i).map (suffixView P i), ?_, fun i vm hci => by simp [hci]⟩
    rcases (Finset.univ \ W).eq_empty_or_nonempty with hemp | hne
    · have hW : W = Finset.univ := by
        ext i; simp only [Finset.mem_univ, iff_true]
        by_contra hiW
        have : i ∈ Finset.univ \ W := by simp [hiW]
        rw [hemp] at this; simp at this
      rw [hW] at hmap
      exact FIReach_mono (fun _ => by simp [ks2]) hmap
    · have hcard1 : (Finset.univ \ W).card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
      have hW : W = Finset.univ.erase p := by
        ext i
        have hmem : i ∉ W ↔ i = p := by
          simpa [Finset.mem_sdiff] using Finset.ext_iff.mp hp i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        tauto
      have eq_ks : (fun _ : Fin (r + 1) => 1) = Fin.cons 1 (fun _ : Fin r => 1) := by
        funext t; cases t using Fin.cases <;> rfl
      rw [hW, eq_ks] at hmap
      have hun := unstrip_FIReach (Finset.mem_univ p) (k₀ := 2) (by omega) hmap
      exact FIReach_mono (fun t => by cases t using Fin.cases <;> simp [ks2]) hun

lemma prefixVert_vert {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {y : Vert P.State (T' + 1)}
    (hy : (KAll P.State Finset.univ (fun _ : Fin (T' + 1) => 1)).vert y) :
    (KAll P.State Finset.univ (ks2 T')).vert (prefixVert P T' y) := by
  obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := hy
  obtain ⟨τ', d, hd, hstep⟩ := prefixCfg_exists P hreach
  refine ⟨Finset.singleton_nonempty _, d, ⟨τ', hd⟩, fun z hz => ?_⟩
  rcases Finset.mem_singleton.mp hz with rfl
  exact hstep y.1 y.2 (hsc y (Finset.mem_singleton_self y))

lemma suffixVert_vert {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {y : Vert P.State (T' + 1)}
    (hy : (KAll P.State Finset.univ (fun _ : Fin (T' + 1) => 1)).vert y) :
    (KAll P.State Finset.univ (ks2 T')).vert (suffixVert P T' y) := by
  obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := hy
  obtain ⟨τ', d, hd, hstep⟩ := suffixCfg_exists P hreach
  refine ⟨Finset.singleton_nonempty _, d, ⟨τ', hd⟩, fun z hz => ?_⟩
  rcases Finset.mem_singleton.mp hz with rfl
  exact hstep y.1 y.2 (hsc y (Finset.mem_singleton_self y))

lemma prefixVert_edge {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {y₁ y₂ : Vert P.State (T' + 1)}
    (hy : (KAll P.State Finset.univ (fun _ : Fin (T' + 1) => 1)).edge y₁ y₂) :
    (KAll P.State Finset.univ (ks2 T')).edge (prefixVert P T' y₁) (prefixVert P T' y₂) := by
  obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := hy
  obtain ⟨τ', d, hd, hstep⟩ := prefixCfg_exists P hreach
  refine ⟨by simp, d, ⟨τ', hd⟩, fun z hz => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hstep y₁.1 y₁.2 (hsc y₁ (by simp))
  · exact hstep y₂.1 y₂.2 (hsc y₂ (by simp))

lemma suffixVert_edge {n : ℕ} {O : Type} (P : Protocol n O) {T' : ℕ}
    {y₁ y₂ : Vert P.State (T' + 1)}
    (hy : (KAll P.State Finset.univ (fun _ : Fin (T' + 1) => 1)).edge y₁ y₂) :
    (KAll P.State Finset.univ (ks2 T')).edge (suffixVert P T' y₁) (suffixVert P T' y₂) := by
  obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := hy
  obtain ⟨τ', d, hd, hstep⟩ := suffixCfg_exists P hreach
  refine ⟨by simp, d, ⟨τ', hd⟩, fun z hz => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hstep y₁.1 y₁.2 (hsc y₁ (by simp))
  · exact hstep y₂.1 y₂.2 (hsc y₂ (by simp))

/-- Lemma 12(b): `outVert P r (suffixVert P r y) = outVert P (r + 1) y`. -/
lemma evalState_suffixView {n : ℕ} {O : Type} (P : Protocol n O) :
    ∀ {r : ℕ} (i : Fin n) (vm : View P.State (r + 1) i),
      evalState P i (suffixView P i vm) = evalState P i vm
  | 0, i, (_, M) => by
      dsimp only [suffixView, evalState]
      congr 1; funext j; cases M j <;> rfl
  | _ + 1, i, (v, M) => by
      dsimp only [suffixView, evalState]
      congr 1; funext j
      cases M j with
      | none => rfl
      | some w => exact congrArg some (evalState_suffixView P j w)

lemma outVert_suffixVert {n : ℕ} {O : Type} (P : Protocol n O) (r : ℕ)
    (y : Vert P.State (r + 1)) :
    outVert P r (suffixVert P r y) = outVert P (r + 1) y :=
  congrArg (P.output y.1) (evalState_suffixView P y.1 y.2)

/-- Lemma 12(c): crash-free evaluation and `suffixView` shift along a crash-free state trajectory. -/
lemma evalState_cleanSubView_univ {n : ℕ} {O : Type} (P : Protocol n O)
    (st : ℕ → (i : Fin n) → P.State i)
    (hst : ∀ t i, st (t + 1) i = P.transition i (fun j => some (st t j))) (t : ℕ) :
    ∀ (r : ℕ) (i : Fin n),
      evalState P i (cleanSubView Finset.univ (st t) r i) = st (t + r) i
  | 0, i => by simp [evalState, cleanSubView]
  | r + 1, i => by
      dsimp only [cleanSubView, evalState]
      have heq : (fun j => (if j ∈ (Finset.univ : Finset (Fin n)) then
          some (cleanSubView Finset.univ (st t) r j) else none).map (evalState P j)) =
          (fun j => some (st (t + r) j)) := by
        funext j; simp [evalState_cleanSubView_univ P st hst t r j]
      rw [heq, ← hst (t + r) i, Nat.add_assoc]

lemma suffixView_cleanSubView_univ {n : ℕ} {O : Type} (P : Protocol n O)
    (st : ℕ → (i : Fin n) → P.State i)
    (hst : ∀ t i, st (t + 1) i = P.transition i (fun j => some (st t j))) (t : ℕ) :
    ∀ (r : ℕ) (i : Fin n),
      suffixView P i (cleanSubView Finset.univ (st t) (r + 1) i) =
      cleanSubView Finset.univ (st (t + 1)) r i
  | 0, i => by
      dsimp only [cleanSubView, suffixView]
      have heq : (fun j => if j ∈ (Finset.univ : Finset (Fin n)) then some (st t j) else none) =
          (fun j => some (st t j)) := by funext j; simp
      rw [heq, ← hst t i]
  | r + 1, i => by
      have ih := suffixView_cleanSubView_univ P st hst t r
      dsimp only [cleanSubView, suffixView]
      refine Prod.ext (ih i) ?_
      funext j
      dsimp only
      have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
      rw [if_pos hj, if_pos hj, Option.map_some]
      exact congrArg some (ih j)

/-! Extending a finite full-information run to an infinite `Execution P` without further crashes -/

structure FITrace {n : ℕ} {State : Fin n → Type} (r : ℕ) (ks : Fin r → ℕ)
    (τ : (i : Fin n) → State i) (c : (i : Fin n) → Option (View State r i)) where
  cfg : (t : ℕ) → t ≤ r → (i : Fin n) → Option (View State t i)
  cfg_zero : cfg 0 (Nat.zero_le r) = initConfig Finset.univ τ
  cfg_last : cfg r (le_refl r) = c
  step : ∀ (t : Fin r), FIRound (ks t) (cfg t.val (Nat.le_of_lt t.isLt))
    (cfg (t.val + 1) t.isLt)

def extendFITrace {n : ℕ} {State : Fin n → Type} {r : ℕ} {ks : Fin (r + 1) → ℕ}
    {τ : (i : Fin n) → State i} {b : (i : Fin n) → Option (View State r i)}
    {c : (i : Fin n) → Option (View State (r + 1) i)}
    (tr : FITrace r (fun s => ks s.castSucc) τ b)
    (hbc : FIRound (ks (Fin.last r)) b c) : FITrace (r + 1) ks τ c where
  cfg t ht :=
    if htr : t ≤ r then tr.cfg t htr
    else (show t = r + 1 by omega) ▸ c
  cfg_zero := by simp [tr.cfg_zero]
  cfg_last := by
    have hnot : ¬ (r + 1 ≤ r) := by omega
    simp [hnot]
  step t := by
    by_cases hlt : t.val < r
    · have h1 : t.val ≤ r := Nat.le_of_lt hlt
      have h2 : t.val + 1 ≤ r := hlt
      have heq_ks : ks t = ks (⟨t.val, hlt⟩ : Fin r).castSucc := by
        congr 1
      rw [dif_pos h1, dif_pos h2, heq_ks]
      exact tr.step ⟨t.val, hlt⟩
    · have htlast : t = Fin.last r := Fin.ext (by have := t.isLt; simp; omega)
      subst htlast
      have h1 : (Fin.last r).val ≤ r := le_refl r
      have h2 : ¬ ((Fin.last r).val + 1 ≤ r) := by simp
      rw [dif_pos h1, dif_neg h2]
      simpa [tr.cfg_last] using hbc

def buildFITrace {n : ℕ} {State : Fin n → Type} (τ : (i : Fin n) → State i) :
    ∀ {r : ℕ} {ks : Fin r → ℕ} {c : (i : Fin n) → Option (View State r i)},
      FIReach r ks (initConfig Finset.univ τ) c → FITrace r ks τ c
  | 0, _, c, hc =>
      { cfg := fun _ ht => (Nat.eq_zero_of_le_zero ht).symm ▸ c
        cfg_zero := hc
        cfg_last := rfl
        step := fun t => Fin.elim0 t }
  | _ + 1, _, _, h =>
      extendFITrace (buildFITrace τ (Classical.choose_spec h).1) (Classical.choose_spec h).2

lemma FIReach_crashes_le {n : ℕ} {State : Fin n → Type} (τ : (i : Fin n) → State i) :
    ∀ {r : ℕ} {ks : Fin r → ℕ} {c : (i : Fin n) → Option (View State r i)},
      FIReach r ks (initConfig Finset.univ τ) c →
      (Finset.univ.filter (fun i => c i = none)).card ≤ ∑ t, ks t
  | 0, _, c, hc => by
      subst hc
      have hemp : Finset.univ.filter (fun i : Fin n => initConfig Finset.univ τ i = none) = ∅ := by
        ext i; simp [initConfig]
      simp [hemp]
  | r + 1, ks, c, ⟨b, hb, hcard, hstep⟩ => by
      have ih := FIReach_crashes_le τ hb
      have hsub : Finset.univ.filter (fun i => c i = none) ⊆
          Finset.univ.filter (fun i => b i = none) ∪
          Finset.univ.filter (fun i => b i ≠ none ∧ c i = none) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
        by_cases hbi : b i = none
        · exact Or.inl hbi
        · exact Or.inr ⟨hbi, hi⟩
      calc (Finset.univ.filter (fun i => c i = none)).card
          ≤ (Finset.univ.filter (fun i => b i = none) ∪
             Finset.univ.filter (fun i => b i ≠ none ∧ c i = none)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun i => b i = none)).card +
            (Finset.univ.filter (fun i => b i ≠ none ∧ c i = none)).card :=
            Finset.card_union_le _ _
        _ ≤ (∑ t : Fin r, ks t.castSucc) + ks (Fin.last r) := Nat.add_le_add ih hcard
        _ = ∑ t : Fin (r + 1), ks t := (Fin.sum_univ_castSucc ks).symm

def extStates {n : ℕ} {O : Type} (P : Protocol n O) (c₀ : Configuration P) :
    ℕ → Configuration P
  | 0 => c₀
  | k + 1 => fun i =>
      if (extStates P c₀ k i).isSome then some (P.transition i (extStates P c₀ k)) else none

lemma extStates_eq_none_iff {n : ℕ} {O : Type} (P : Protocol n O) (c₀ : Configuration P)
    (k : ℕ) (i : Fin n) :
    extStates P c₀ k i = none ↔ c₀ i = none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [extStates]
    cases hk : extStates P c₀ k i with
    | none => simp [ih.mp hk]
    | some s =>
      have hc0 : c₀ i ≠ none := fun h => by rw [ih.mpr h] at hk; cases hk
      simp [hc0]

def traceToExecution {n : ℕ} {O : Type} (P : Protocol n O) {r : ℕ} {ks : Fin r → ℕ}
    {τ : (i : Fin n) → P.State i} {c : (i : Fin n) → Option (View P.State r i)}
    (tr : FITrace r ks τ c) : Execution P where
  config t :=
    if ht : t ≤ r then fun i => (tr.cfg t ht i).map (evalState P i)
    else extStates P (fun i => (c i).map (evalState P i)) (t - r)
  messages t :=
    if ht : t < r then
      fun i => match tr.cfg (t + 1) ht i with
        | some vm => fun j => (vm.2 j).map (evalState P j)
        | none => fun _ => none
    else fun _ => extStates P (fun i => (c i).map (evalState P i)) (t - r)
  initial i := by
    have h0 : 0 ≤ r := Nat.zero_le r
    simp [h0, tr.cfg_zero, initConfig, evalState]
  step t := by
    by_cases ht : t < r
    · have ht_le : t ≤ r := Nat.le_of_lt ht
      have ht1_le : t + 1 ≤ r := ht
      intro i s' hs'
      simp only [ht_le, ht1_le, ht, ↓reduceDIte] at hs' ⊢
      obtain ⟨vm, hvm, rfl⟩ := opt_map_eq_some.mp hs'
      obtain ⟨hbi, hM, hsurv⟩ := (tr.step ⟨t, ht⟩).2 i vm hvm
      simp only [hvm]
      refine ⟨⟨evalState P i vm.1, by simp [hbi]⟩, fun j => ?_, fun j hj => ?_, rfl⟩
      · rcases hM j with h0 | h1
        · exact Or.inl (by simp [h0])
        · exact Or.inr (by simp [h1])
      · have hcj : tr.cfg (t + 1) ht1_le j ≠ none := by intro h0; simp [h0] at hj
        simp [hsurv j hcj]
    · have hrt : r ≤ t := Nat.le_of_not_lt ht
      have ht1_not : ¬ (t + 1 ≤ r) := by omega
      have hsub : t + 1 - r = (t - r) + 1 := by omega
      have hcfg_t : (if h : t ≤ r then fun i => (tr.cfg t h i).map (evalState P i)
          else extStates P (fun i => (c i).map (evalState P i)) (t - r)) =
          extStates P (fun i => (c i).map (evalState P i)) (t - r) := by
        split_ifs with h
        · have hteq : t = r := by omega
          subst hteq; simp [tr.cfg_last, extStates]
        · rfl
      intro i s' hs'
      simp only [ht1_not, ht, ↓reduceDIte, hsub] at hs' ⊢
      rw [hcfg_t]
      dsimp only [extStates] at hs'
      split_ifs at hs' with his
      simp only [Option.some.injEq] at hs'
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp his
      exact ⟨⟨s, hs⟩, fun _ => Or.inr rfl, fun _ _ => rfl, hs'.symm⟩

lemma traceCfg_none_imp_last_none {n : ℕ} {State : Fin n → Type} {r : ℕ} {ks : Fin r → ℕ}
    {τ : (i : Fin n) → State i} {c : (i : Fin n) → Option (View State r i)}
    (tr : FITrace r ks τ c) (i : Fin n) :
    ∀ (t : ℕ) (ht : t ≤ r), tr.cfg t ht i = none → c i = none := by
  intro t ht hnone
  suffices ∀ (d : ℕ) (t : ℕ) (ht : t ≤ r), r - t = d → tr.cfg t ht i = none → c i = none from
    this (r - t) t ht rfl hnone
  intro d
  induction d with
  | zero =>
    intro t ht hd hnone
    have htr : t = r := by omega
    subst htr; rwa [← tr.cfg_last]
  | succ d ih =>
    intro t ht hd hnone
    have hlt : t < r := by omega
    have hnext : tr.cfg (t + 1) hlt i = none := by
      by_contra hne
      obtain ⟨vm, hvm⟩ := Option.ne_none_iff_exists'.mp hne
      have hbi := ((tr.step ⟨t, hlt⟩).2 i vm hvm).1
      rw [hnone] at hbi; cases hbi
    exact ih (t + 1) hlt (by omega) hnext

lemma traceToExecution_nonfaulty_iff {n : ℕ} {O : Type} (P : Protocol n O) {r : ℕ} {ks : Fin r → ℕ}
    {τ : (i : Fin n) → P.State i} {c : (i : Fin n) → Option (View P.State r i)}
    (tr : FITrace r ks τ c) (i : Fin n) :
    Nonfaulty (traceToExecution P tr) i ↔ c i ≠ none := by
  constructor
  · intro hnf hci
    have hr : (traceToExecution P tr).config r i = none := by
      simp [traceToExecution, tr.cfg_last, hci]
    exact hnf r hr
  · intro hci t
    dsimp only [traceToExecution]
    split_ifs with ht
    · intro hnone
      have htr_none : tr.cfg t ht i = none := by
        cases h : tr.cfg t ht i <;> simp [h] at hnone ⊢
      exact hci (traceCfg_none_imp_last_none tr i t ht htr_none)
    · intro hnone
      rw [extStates_eq_none_iff] at hnone
      cases hc : c i <;> simp [hc] at hnone hci

lemma traceToExecution_atMostCrashes {n : ℕ} {O : Type} (P : Protocol n O) {r : ℕ} {ks : Fin r → ℕ}
    {τ : (i : Fin n) → P.State i} {c : (i : Fin n) → Option (View P.State r i)}
    (tr : FITrace r ks τ c) (hreach : FIReach r ks (initConfig Finset.univ τ) c)
    {f : ℕ} (hf : ∑ t, ks t ≤ f) :
    AtMostCrashes (traceToExecution P tr) f := by
  have heq : Finset.univ.filter (fun i => ∃ t, (traceToExecution P tr).config t i = none) =
      Finset.univ.filter (fun i => c i = none) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hnf := traceToExecution_nonfaulty_iff P tr i
    dsimp only [Nonfaulty] at hnf
    by_cases hci : c i = none
    · simp only [hci, iff_true]
      exact ⟨r, by simp [traceToExecution, tr.cfg_last, hci]⟩
    · simp only [hci, iff_false]
      push Not
      exact hnf.mpr hci
  dsimp only [AtMostCrashes]
  rw [heq]
  exact (FIReach_crashes_le τ hreach).trans hf

/-! Cycle offsets, cocycle property (Lemmas 13–14), potential `ℓ` (Lemma 15), and advancement (Lemmas 16–17) -/

def cycleOffset (q s : ℕ) (a b : ℤ) : ℤ :=
  let r := (b - a) % (q : ℤ)
  if r ≤ (s : ℤ) then r else r - (q : ℤ)

lemma cycleOffset_exists_mul {q s : ℕ} (a b : ℤ) :
    ∃ k : ℤ, cycleOffset q s a b = (b - a) + k * (q : ℤ) := by
  dsimp only [cycleOffset]
  have hdiv := Int.emod_add_mul_ediv (b - a) (q : ℤ)
  split_ifs
  · exact ⟨-((b - a) / (q : ℤ)), by linarith⟩
  · exact ⟨-((b - a) / (q : ℤ)) - 1, by linarith⟩

lemma cycleOffset_eq_of_lift {q s : ℕ} (hqs : 2 * s < q) {a b La Lb : ℤ}
    (ha : a = La % (q : ℤ)) (hb : b = Lb % (q : ℤ)) (hdiff : |Lb - La| ≤ (s : ℤ)) :
    cycleOffset q s a b = Lb - La := by
  have hbounds := abs_le.mp hdiff
  have hmod : (b - a) % (q : ℤ) = (Lb - La) % (q : ℤ) := by
    rw [ha, hb, ← Int.sub_emod]
  dsimp only [cycleOffset]
  rw [hmod]
  by_cases h0 : 0 ≤ Lb - La
  · have hlt : Lb - La < (q : ℤ) := by omega
    rw [Int.emod_eq_of_lt h0 hlt, if_pos hbounds.2]
  · have hsum_eq : Lb - La = (Lb - La + (q : ℤ)) + (-1) * (q : ℤ) := by ring
    have hpos : 0 ≤ Lb - La + (q : ℤ) := by omega
    have hlt : Lb - La + (q : ℤ) < (q : ℤ) := by omega
    have hrem : (Lb - La) % (q : ℤ) = Lb - La + (q : ℤ) := by
      conv_lhs => rw [hsum_eq]
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt hpos hlt]
    have hgt : ¬ (Lb - La + (q : ℤ) ≤ (s : ℤ)) := by omega
    rw [hrem, if_neg hgt]
    omega

def outInt {n q : ℕ} (P : Protocol n (Fin q)) (r : ℕ) (x : Vert P.State r) : ℤ :=
  (outVert P r x).val

def adv {n q : ℕ} (P : Protocol n (Fin q)) (r : ℕ) (y : Vert P.State (r + 1)) : ℤ :=
  (outInt P r (suffixVert P r y) - outInt P r (prefixVert P r y)) % (q : ℤ)

/-- Theorem 6: Non-trivial counting lower bound. -/
theorem theorem_6 {n f s q : ℕ} (P : Protocol n (Fin q))
    (hf : 1 ≤ f) (hn : f + 2 < n) (hq : max (2 * s) 1 < q) :
    ¬ CountingResilient P f s (f / 2) := by
  rintro ⟨hLift, hNontriv⟩
  have h2s : 2 * s < q := lt_of_le_of_lt (le_max_left _ _) hq
  have h1q : 1 < q := lt_of_le_of_lt (le_max_right _ _) hq
  have hq_pos : (0 : ℤ) < (q : ℤ) := by omega
  let T' : ℕ := f / 2
  let X := KAll P.State Finset.univ (ks2 T')
  let Y := KAll P.State Finset.univ (fun _ : Fin (T' + 1) => 1)
  have hX_C1 : X.C1 := by
    refine (K_C1 T' P.State Finset.univ ?_).2
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hY_C0 : Y.C0 := by
    refine (K_C0 (T' + 1) P.State Finset.univ (fun _ => 1)
      (fun _ => le_refl 1) (fun _ _ _ => le_refl 1) ?_).2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  -- Clock offset map D on X and cocycle property (Lemmas 13–14)
  let D : Vert P.State T' → Vert P.State T' → ℤ :=
    fun u v => cycleOffset q s (outInt P T' u) (outInt P T' v)
  have hCocycle : X.IsCocycle D := by
    intro u v w htri
    obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := htri
    let tr := buildFITrace τ hreach
    let e := traceToExecution P tr
    have hcrashes : AtMostCrashes e f := by
      refine traceToExecution_atMostCrashes P tr hreach ?_
      simp only [ks2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    obtain ⟨L, hL⟩ := hLift e hcrashes
    obtain ⟨hL1, hL2, _⟩ := hL T' (le_refl T')
    have hcu : c u.1 = some u.2 := hsc u (by simp)
    have hcv : c v.1 = some v.2 := hsc v (by simp)
    have hcw : c w.1 = some w.2 := hsc w (by simp)
    have hnfu : Nonfaulty e u.1 := (traceToExecution_nonfaulty_iff P tr u.1).mpr (by simp [hcu])
    have hnfv : Nonfaulty e v.1 := (traceToExecution_nonfaulty_iff P tr v.1).mpr (by simp [hcv])
    have hnfw : Nonfaulty e w.1 := (traceToExecution_nonfaulty_iff P tr w.1).mpr (by simp [hcw])
    have hou : outInt P T' u = L u.1 T' % (q : ℤ) :=
      hL1 u.1 hnfu (evalState P u.1 u.2) (by simp [e, traceToExecution, tr.cfg_last, hcu])
    have hov : outInt P T' v = L v.1 T' % (q : ℤ) :=
      hL1 v.1 hnfv (evalState P v.1 v.2) (by simp [e, traceToExecution, tr.cfg_last, hcv])
    have how : outInt P T' w = L w.1 T' % (q : ℤ) :=
      hL1 w.1 hnfw (evalState P w.1 w.2) (by simp [e, traceToExecution, tr.cfg_last, hcw])
    have hDuv : D u v = L v.1 T' - L u.1 T' :=
      cycleOffset_eq_of_lift h2s hou hov (hL2 v.1 u.1 hnfv hnfu)
    have hDvw : D v w = L w.1 T' - L v.1 T' :=
      cycleOffset_eq_of_lift h2s hov how (hL2 w.1 v.1 hnfw hnfv)
    have hDuw : D u w = L w.1 T' - L u.1 T' :=
      cycleOffset_eq_of_lift h2s hou how (hL2 w.1 u.1 hnfw hnfu)
    omega
  -- Potential ℓ on X (Lemma 15)
  obtain ⟨ϑ, hϑ⟩ := hX_C1.2 D hCocycle
  obtain ⟨b₀, hb₀⟩ := hX_C1.1.1
  let ℓ : Vert P.State T' → ℤ := fun u => ϑ u - ϑ b₀ + outInt P T' b₀
  have hℓ_edge : ∀ u v, X.edge u v → ℓ v - ℓ u = D u v := by
    intro u v huv
    have := hϑ u v huv
    dsimp only [ℓ]
    omega
  have hℓ_mod : ∀ u, X.vert u → ℓ u % (q : ℤ) = outInt P T' u := by
    let g : Vert P.State T' → ℤ := fun x => (ℓ x - outInt P T' x) % (q : ℤ)
    have hg_edge : ∀ u v, X.edge u v → g u = g v := by
      intro u v huv
      have he := hℓ_edge u v huv
      obtain ⟨k, hk⟩ := cycleOffset_exists_mul (q := q) (s := s) (outInt P T' u) (outInt P T' v)
      have hrel : ℓ v - outInt P T' v = (ℓ u - outInt P T' u) + k * (q : ℤ) := by
        dsimp only [D] at he; linarith
      dsimp only [g]
      rw [hrel, Int.add_mul_emod_self_right]
    intro u hu
    have hgu : g u = g b₀ := hX_C1.1.2 g hg_edge u b₀ hu hb₀
    have hgb₀ : g b₀ = 0 := by simp [g, ℓ]
    have hgu0 : (ℓ u - outInt P T' u) % (q : ℤ) = 0 := hgu.trans hgb₀
    have hdiv := Int.emod_add_mul_ediv (ℓ u - outInt P T' u) (q : ℤ)
    rw [hgu0, zero_add] at hdiv
    have hlu : ℓ u = outInt P T' u + (q : ℤ) * ((ℓ u - outInt P T' u) / (q : ℤ)) := by
      linarith
    rw [hlu, mul_comm (q : ℤ), Int.add_mul_emod_self_right]
    dsimp only [outInt]
    exact Int.emod_eq_of_lt (Nat.cast_nonneg _) (Nat.cast_lt.mpr (outVert P T' u).isLt)
  -- Offset consistency across rounds (Lemma 16)
  have hConsistency : ∀ y₁ y₂, Y.edge y₁ y₂ →
      D (suffixVert P T' y₁) (suffixVert P T' y₂) + adv P T' y₁ =
      D (prefixVert P T' y₁) (prefixVert P T' y₂) + adv P T' y₂ := by
    intro y₁ y₂ hy
    obtain ⟨_, c, ⟨τ, hreach⟩, hsc⟩ := hy
    obtain ⟨b, hb, hbc⟩ := hreach
    let tr₀ := buildFITrace τ hb
    let tr := extendFITrace (ks := fun _ : Fin (T' + 1) => 1) tr₀ hbc
    let e := traceToExecution P tr
    have hcrashes : AtMostCrashes e f := by
      refine traceToExecution_atMostCrashes P tr ⟨b, hb, hbc⟩ ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      omega
    obtain ⟨L, hL⟩ := hLift e hcrashes
    obtain ⟨hL1_T, hL2_T, hL3_T⟩ := hL T' (le_refl T')
    obtain ⟨hL1_T1, hL2_T1, _⟩ := hL (T' + 1) (Nat.le_succ T')
    have hcy₁ : c y₁.1 = some y₁.2 := hsc y₁ (by simp)
    have hcy₂ : c y₂.1 = some y₂.2 := hsc y₂ (by simp)
    have hby₁ : b y₁.1 = some y₁.2.1 := (hbc.2 y₁.1 y₁.2 hcy₁).1
    have hby₂ : b y₂.1 = some y₂.2.1 := (hbc.2 y₂.1 y₂.2 hcy₂).1
    have hnfy₁ : Nonfaulty e y₁.1 := (traceToExecution_nonfaulty_iff P tr y₁.1).mpr (by simp [hcy₁])
    have hnfy₂ : Nonfaulty e y₂.1 := (traceToExecution_nonfaulty_iff P tr y₂.1).mpr (by simp [hcy₂])
    have hcfg_T : ∀ i, e.config T' i = (b i).map (evalState P i) := by
      intro i
      have hle : T' ≤ T' + 1 := Nat.le_succ T'
      simp [e, traceToExecution, hle, tr, extendFITrace, tr₀.cfg_last]
    have hcfg_T1 : ∀ i, e.config (T' + 1) i = (c i).map (evalState P i) := by
      intro i
      simp [e, traceToExecution, tr.cfg_last]
    have hop₁ : outInt P T' (prefixVert P T' y₁) = L y₁.1 T' % (q : ℤ) :=
      hL1_T y₁.1 hnfy₁ _ (by simp [hcfg_T, hby₁, prefixVert])
    have hop₂ : outInt P T' (prefixVert P T' y₂) = L y₂.1 T' % (q : ℤ) :=
      hL1_T y₂.1 hnfy₂ _ (by simp [hcfg_T, hby₂, prefixVert])
    have hos₁ : outInt P T' (suffixVert P T' y₁) = L y₁.1 (T' + 1) % (q : ℤ) := by
      dsimp only [outInt]
      rw [outVert_suffixVert]
      exact hL1_T1 y₁.1 hnfy₁ _ (by simp [hcfg_T1, hcy₁])
    have hos₂ : outInt P T' (suffixVert P T' y₂) = L y₂.1 (T' + 1) % (q : ℤ) := by
      dsimp only [outInt]
      rw [outVert_suffixVert]
      exact hL1_T1 y₂.1 hnfy₂ _ (by simp [hcfg_T1, hcy₂])
    have hDP : D (prefixVert P T' y₁) (prefixVert P T' y₂) = L y₂.1 T' - L y₁.1 T' :=
      cycleOffset_eq_of_lift h2s hop₁ hop₂ (hL2_T y₂.1 y₁.1 hnfy₂ hnfy₁)
    have hDS : D (suffixVert P T' y₁) (suffixVert P T' y₂) = L y₂.1 (T' + 1) - L y₁.1 (T' + 1) :=
      cycleOffset_eq_of_lift h2s hos₁ hos₂ (hL2_T1 y₂.1 y₁.1 hnfy₂ hnfy₁)
    have hadv₁ : adv P T' y₁ = L y₁.1 (T' + 1) - L y₁.1 T' := by
      dsimp only [adv]
      rw [hos₁, hop₁, ← Int.sub_emod,
        Int.emod_eq_of_lt (hL3_T y₁.1 hnfy₁).1 (hL3_T y₁.1 hnfy₁).2]
    have hadv₂ : adv P T' y₂ = L y₂.1 (T' + 1) - L y₂.1 T' := by
      dsimp only [adv]
      rw [hos₂, hop₂, ← Int.sub_emod,
        Int.emod_eq_of_lt (hL3_T y₂.1 hnfy₂).1 (hL3_T y₂.1 hnfy₂).2]
    omega
  -- Constant wraparound shift c ∈ ℤ on Y (Lemma 17)
  let ε : Vert P.State (T' + 1) → ℤ :=
    fun y => ℓ (suffixVert P T' y) - ℓ (prefixVert P T' y) - adv P T' y
  have hε_edge : ∀ y₁ y₂, Y.edge y₁ y₂ → ε y₁ = ε y₂ := by
    intro y₁ y₂ hy
    have hS := hℓ_edge (suffixVert P T' y₁) (suffixVert P T' y₂) (suffixVert_edge P hy)
    have hP := hℓ_edge (prefixVert P T' y₁) (prefixVert P T' y₂) (prefixVert_edge P hy)
    have hC := hConsistency y₁ y₂ hy
    dsimp only [ε]
    omega
  obtain ⟨y₀, hy₀⟩ := hY_C0.1
  let c_shift : ℤ := (ℓ (suffixVert P T' y₀) - ℓ (prefixVert P T' y₀)) / (q : ℤ)
  have hε_y₀ : ε y₀ = (q : ℤ) * c_shift := by
    have hs := hℓ_mod (suffixVert P T' y₀) (suffixVert_vert P hy₀)
    have hp := hℓ_mod (prefixVert P T' y₀) (prefixVert_vert P hy₀)
    have hrem : (ℓ (suffixVert P T' y₀) - ℓ (prefixVert P T' y₀)) % (q : ℤ) = adv P T' y₀ := by
      rw [Int.sub_emod, hs, hp]; rfl
    have hdiv := Int.emod_add_mul_ediv (ℓ (suffixVert P T' y₀) - ℓ (prefixVert P T' y₀)) (q : ℤ)
    rw [hrem] at hdiv
    dsimp only [ε, c_shift]
    linarith
  have hLemma17 : ∀ y, Y.vert y →
      ℓ (suffixVert P T' y) - ℓ (prefixVert P T' y) = adv P T' y + (q : ℤ) * c_shift := by
    intro y hy
    have heq : ε y = ε y₀ := hY_C0.2 ε hε_edge y y₀ hy hy₀
    rw [hε_y₀] at heq
    dsimp only [ε] at heq
    linarith
  -- Contradiction from Nontrivial P and finiteness of Vert P.State T'
  obtain ⟨e, he0, i₀, hinf⟩ := hNontriv
  have he_ne : ∀ t j, e.config t j ≠ none := by
    intro t j hnone
    dsimp only [AtMostCrashes] at he0
    have hmem : j ∈ Finset.univ.filter (fun l => ∃ t', e.config t' l = none) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t, hnone⟩
    have hpos : 0 < (Finset.univ.filter (fun l => ∃ t', e.config t' l = none)).card :=
      Finset.card_pos.mpr ⟨j, hmem⟩
    omega
  let st : ℕ → (j : Fin n) → P.State j :=
    fun t j => (e.config t j).get (Option.isSome_iff_ne_none.mpr (he_ne t j))
  have hst_some : ∀ t j, e.config t j = some (st t j) :=
    fun t j => (Option.some_get _).symm
  have hst_step : ∀ t j, st (t + 1) j = P.transition j (fun l => some (st t l)) := by
    intro t j
    obtain ⟨_, _, hsurv, htr⟩ := e.step t j (st (t + 1) j) (hst_some (t + 1) j)
    have hmsg : e.messages t j = fun l => some (st t l) := by
      funext l
      rw [hsurv l (he_ne (t + 1) l), hst_some t l]
    rwa [hmsg] at htr
  let xSeq : ℕ → Vert P.State T' := fun t => ⟨i₀, cleanSubView Finset.univ (st t) T' i₀⟩
  let ySeq : ℕ → Vert P.State (T' + 1) := fun t => ⟨i₀, cleanSubView Finset.univ (st t) (T' + 1) i₀⟩
  have hySeq_vert : ∀ t, Y.vert (ySeq t) := by
    intro t
    refine ⟨Finset.singleton_nonempty _, cleanSubCfg Finset.univ (st t) (T' + 1),
      ⟨st t, FIReach_cleanSubCfg Finset.univ (st t) (T' + 1) _⟩, ?_⟩
    intro z hz; rcases Finset.mem_singleton.mp hz with rfl
    simp [cleanSubCfg, ySeq]
  have hPy : ∀ t, prefixVert P T' (ySeq t) = xSeq t := fun _ => rfl
  have hSy : ∀ t, suffixVert P T' (ySeq t) = xSeq (t + 1) := by
    intro t
    exact Sigma.ext rfl (heq_of_eq (suffixView_cleanSubView_univ P st hst_step t T' i₀))
  have hStep_ℓ : ∀ t, ℓ (xSeq (t + 1)) - ℓ (xSeq t) = adv P T' (ySeq t) + (q : ℤ) * c_shift := by
    intro t
    have h := hLemma17 (ySeq t) (hySeq_vert t)
    rwa [hPy t, hSy t] at h
  have hadv_bounds : ∀ t, 0 ≤ adv P T' (ySeq t) ∧ adv P T' (ySeq t) < (q : ℤ) :=
    fun t => ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hq_pos⟩
  have hex_pos : ∀ M : ℕ, ∃ t ≥ M, 1 ≤ adv P T' (ySeq t) := by
    intro M
    obtain ⟨t', ht', s₁, s₂, hs₁, hs₂, hne⟩ := hinf (M + T')
    let t := t' - T'
    have ht_eq : t + T' = t' := by omega
    have hs₁_eq : s₁ = st (t + T') i₀ := by
      rw [ht_eq]
      exact Option.some.inj (hs₁.symm.trans (hst_some t' i₀))
    have hs₂_eq : s₂ = st ((t + 1) + T') i₀ := by
      have : (t + 1) + T' = t' + 1 := by omega
      rw [this]
      exact Option.some.inj (hs₂.symm.trans (hst_some (t' + 1) i₀))
    have hout_x : ∀ r, outVert P T' (xSeq r) = P.output i₀ (st (r + T') i₀) := by
      intro r
      dsimp only [outVert, xSeq]
      rw [evalState_cleanSubView_univ P st hst_step r T' i₀]
    have hne_out : outVert P T' (xSeq t) ≠ outVert P T' (xSeq (t + 1)) := by
      rw [hout_x t, hout_x (t + 1), ← hs₁_eq, ← hs₂_eq]
      exact hne
    have hadv_ne : adv P T' (ySeq t) ≠ 0 := by
      intro h0
      dsimp only [adv] at h0
      rw [hPy t, hSy t] at h0
      have hdiv := Int.emod_add_mul_ediv (outInt P T' (xSeq (t + 1)) - outInt P T' (xSeq t)) (q : ℤ)
      rw [h0, zero_add] at hdiv
      have hlt1 : outInt P T' (xSeq t) < (q : ℤ) := Nat.cast_lt.mpr (outVert P T' (xSeq t)).isLt
      have hlt2 : outInt P T' (xSeq (t + 1)) < (q : ℤ) := Nat.cast_lt.mpr (outVert P T' (xSeq (t + 1))).isLt
      have hnn1 : (0 : ℤ) ≤ outInt P T' (xSeq t) := Nat.cast_nonneg _
      have hnn2 : (0 : ℤ) ≤ outInt P T' (xSeq (t + 1)) := Nat.cast_nonneg _
      let k := (outInt P T' (xSeq (t + 1)) - outInt P T' (xSeq t)) / (q : ℤ)
      have hk0 : k = 0 := by
        by_contra hkne
        rcases lt_or_gt_of_ne hkne with hklt | hkgt
        · have : (q : ℤ) * k ≤ -(q : ℤ) := by nlinarith
          linarith
        · have : (q : ℤ) ≤ (q : ℤ) * k := by nlinarith
          linarith
      change (q : ℤ) * k = _ at hdiv
      rw [hk0, mul_zero] at hdiv
      dsimp only [outInt] at hdiv
      have hval_eq : (outVert P T' (xSeq (t + 1))).val = (outVert P T' (xSeq t)).val := by omega
      exact hne_out (Fin.ext hval_eq.symm)
    refine ⟨t, by omega, ?_⟩
    have := (hadv_bounds t).1
    omega
  let B : ℕ := Finset.univ.sup (fun u : Vert P.State T' => (ℓ u).natAbs)
  have hℓ_bound : ∀ u : Vert P.State T', -(B : ℤ) ≤ ℓ u ∧ ℓ u ≤ (B : ℤ) := by
    intro u
    have hsup : (ℓ u).natAbs ≤ B := Finset.le_sup (f := fun z : Vert P.State T' => (ℓ z).natAbs) (Finset.mem_univ u)
    omega
  rcases le_or_gt 0 c_shift with hc | hc
  · have hmono : ∀ t₁ t₂, t₁ ≤ t₂ → ℓ (xSeq t₁) ≤ ℓ (xSeq t₂) := by
      intro t₁ t₂ hle
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      induction d with
      | zero => simp
      | succ d ih =>
        have ih' := ih (Nat.le_add_right t₁ d)
        have hstep := hStep_ℓ (t₁ + d)
        have hadv0 := (hadv_bounds (t₁ + d)).1
        have hqc0 : 0 ≤ (q : ℤ) * c_shift := mul_nonneg (by omega) hc
        rw [show t₁ + (d + 1) = (t₁ + d) + 1 by omega]
        linarith
    have hgrow : ∀ k : ℕ, ∃ t : ℕ, ℓ (xSeq 0) + (k : ℤ) ≤ ℓ (xSeq t) := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨tk, htk⟩ := ih
        obtain ⟨t, htle, hadv1⟩ := hex_pos tk
        have hmono_t := hmono tk t htle
        have hstep := hStep_ℓ t
        have hqc0 : 0 ≤ (q : ℤ) * c_shift := mul_nonneg (by omega) hc
        exact ⟨t + 1, by push_cast; linarith⟩
    obtain ⟨t_big, ht_big⟩ := hgrow (2 * B + 1)
    have hb0 := hℓ_bound (xSeq 0)
    have hbt := hℓ_bound (xSeq t_big)
    push_cast at ht_big
    omega
  · have hshrink : ∀ k : ℕ, ℓ (xSeq k) ≤ ℓ (xSeq 0) - (k : ℤ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hstep := hStep_ℓ k
        have hadv_lt := (hadv_bounds k).2
        have hqc_le : (q : ℤ) * c_shift ≤ -(q : ℤ) := by nlinarith
        push_cast
        linarith
    have h_small := hshrink (2 * B + 1)
    have hb0 := hℓ_bound (xSeq 0)
    have hbt := hℓ_bound (xSeq (2 * B + 1))
    push_cast at h_small
    omega

/-! ### Part 4: Pulse-to-Counting Reduction (Section 2.3 / Lemma 8) and Theorem 2 -/

def effCounter {n : ℕ} (P : Protocol n Bool) (s : ℕ) (i : Fin n)
    (sc : P.State i × Fin (2 * s + 1)) : Fin (2 * s + 1) :=
  if P.output i sc.1 then ⟨0, by omega⟩ else sc.2

@[reducible] def pulseToCounting {n : ℕ} (P : Protocol n Bool) (s : ℕ) : Protocol n (Fin (2 * s + 1)) where
  State i := P.State i × Fin (2 * s + 1)
  finiteState _ := inferInstance
  nonemptyState _ := inferInstance
  transition i M :=
    let st' := P.transition i (fun j => (M j).map Prod.fst)
    if P.output i st' then
      (st', ⟨0, by omega⟩)
    else
      let prev : ℕ := match M i with
        | some old => (effCounter P s i old).val
        | none => 0
      (st', ⟨min (2 * s) (prev + 1), by omega⟩)
  output i sc := effCounter P s i sc

def projExecution {n : ℕ} (P : Protocol n Bool) (s : ℕ)
    (e : Execution (pulseToCounting P s)) : Execution P where
  config t i := (e.config t i).map Prod.fst
  messages t i j := (e.messages t i j).map Prod.fst
  initial i := by
    obtain ⟨sc, hsc⟩ := e.initial i
    exact ⟨sc.1, by simp [hsc]⟩
  step t i st' hst' := by
    obtain ⟨sc', hsc', rfl⟩ := opt_map_eq_some.mp hst'
    obtain ⟨⟨sc, hsc⟩, hM, hsurv, htr⟩ := e.step t i sc' hsc'
    refine ⟨⟨sc.1, by simp [hsc]⟩, fun j => ?_, fun j hj => ?_, ?_⟩
    · rcases hM j with h0 | h1
      · exact Or.inl (by simp [h0])
      · exact Or.inr (by simp [h1])
    · have hcj : e.config (t + 1) j ≠ none := by intro h0; simp [h0] at hj
      simp [hsurv j hcj]
    · rw [htr]
      dsimp only [pulseToCounting]
      split_ifs <;> rfl

lemma projExecution_nonfaulty_iff {n : ℕ} (P : Protocol n Bool) (s : ℕ)
    (e : Execution (pulseToCounting P s)) (i : Fin n) :
    Nonfaulty (projExecution P s e) i ↔ Nonfaulty e i := by
  dsimp only [Nonfaulty, projExecution]
  exact forall_congr' fun t => by cases e.config t i <;> simp

lemma projExecution_atMostCrashes {n : ℕ} (P : Protocol n Bool) (s : ℕ)
    (e : Execution (pulseToCounting P s)) {f : ℕ} (hf : AtMostCrashes e f) :
    AtMostCrashes (projExecution P s e) f := by
  dsimp only [AtMostCrashes, projExecution] at hf ⊢
  have heq : (Finset.univ.filter fun i => ∃ t, (e.config t i).map Prod.fst = none) =
      (Finset.univ.filter fun i => ∃ t, e.config t i = none) := by
    ext i; simp
  rw [heq]; exact hf

/-- Counter dynamics of a non-faulty process in `pulseToCounting P s`. -/
lemma counter_pulse_zero {n : ℕ} (P : Protocol n Bool) (s : ℕ)
    (e : Execution (pulseToCounting P s)) (i : Fin n) (t : ℕ)
    (sc : P.State i × Fin (2 * s + 1)) (hsc : e.config t i = some sc)
    (hp : Pulses (projExecution P s e) i t) :
    ((pulseToCounting P s).output i sc).val = 0 := by
  obtain ⟨st, hst, hout⟩ := hp
  dsimp only [projExecution] at hst
  rw [hsc] at hst
  simp only [Option.map_some, Option.some.injEq] at hst
  subst hst
  simp [pulseToCounting, effCounter, hout]

lemma counter_step_no_pulse {n : ℕ} (P : Protocol n Bool) (s : ℕ)
    (e : Execution (pulseToCounting P s)) (i : Fin n) (t : ℕ)
    (sc₀ sc₁ : P.State i × Fin (2 * s + 1))
    (hsc₀ : e.config t i = some sc₀) (hsc₁ : e.config (t + 1) i = some sc₁)
    (hnp : ¬ Pulses (projExecution P s e) i (t + 1)) :
    ((pulseToCounting P s).output i sc₁).val =
    min (2 * s) (((pulseToCounting P s).output i sc₀).val + 1) := by
  have hout_false : P.output i sc₁.1 = false := by
    cases h : P.output i sc₁.1 with
    | false => rfl
    | true =>
      exfalso; apply hnp
      exact ⟨sc₁.1, by simp [projExecution, hsc₁], h⟩
  obtain ⟨_, _, hsurv, htr⟩ := e.step t i sc₁ hsc₁
  have hMii : e.messages t i i = some sc₀ := by
    rw [hsurv i (by simp [hsc₁]), hsc₀]
  have hsc₁_fst : P.transition i (fun j => (e.messages t i j).map Prod.fst) = sc₁.1 := by
    have := congrArg Prod.fst htr
    dsimp only [pulseToCounting] at this
    split_ifs at this <;> exact this.symm
  dsimp only [pulseToCounting] at htr
  rw [hsc₁_fst, if_neg (by simp [hout_false])] at htr
  have hval := congrArg (fun x : P.State i × Fin (2 * s + 1) => x.2.val) htr
  dsimp only at hval
  rw [hMii] at hval
  dsimp only [pulseToCounting, effCounter]
  rw [if_neg (by simp [hout_false])]
  exact hval

/-- Integer interval extraction from real-skew `PulseExecution`. -/
lemma nat_pulse_intervals {n : ℕ} {P : Protocol n Bool} {eP : Execution P}
    {σ : ℝ} {T : ℕ} (hσ : 1 ≤ σ) (hpe : PulseExecution eP σ T) :
    let s := Nat.floor σ
    ∃ a b : ℕ → ℕ, a 0 ≤ T ∧ ∀ k,
      a k ≤ b k ∧ b k - a k ≤ s ∧
      (∀ i, Nonfaulty eP i → ∃! t : ℕ, a k ≤ t ∧ t ≤ b k ∧ Pulses eP i t) ∧
      b k + s < a (k + 1) ∧
      (∀ i, Nonfaulty eP i → ∀ t, b k < t → t < a (k + 1) → ¬ Pulses eP i t) := by
  intro s
  have hs_le : (s : ℝ) ≤ σ := Nat.floor_le (by linarith)
  have hσ_lt : σ < (s : ℝ) + 1 := Nat.lt_floor_add_one σ
  obtain ⟨a, b, ha0, hk⟩ := hpe
  refine ⟨a, b, ha0, fun k => ?_⟩
  obtain ⟨hab, hskew, hex, hsep, hgap⟩ := hk k
  refine ⟨hab, ?_, hex, ?_, hgap⟩
  · by_contra hgt
    have hle : a k + s + 1 ≤ b k := by omega
    have hreal : (a k : ℝ) + (s : ℝ) + 1 ≤ (b k : ℝ) := by exact_mod_cast hle
    linarith
  · have hreal : ((b k + s : ℕ) : ℝ) < (a (k + 1) : ℝ) := by push_cast; linarith
    exact Nat.cast_lt.mp hreal

/-- N2: `pulseToCounting P s` is `Nontrivial` when `P` is `PulseResilient`. -/
lemma pulseToCounting_nontrivial {n f T : ℕ} {σ : ℝ} (P : Protocol n Bool)
    (hσ : 1 ≤ σ) (hn : f + 2 < n) (hP : PulseResilient P f σ T) :
    let s := Nat.floor σ
    Nontrivial (pulseToCounting P s) := by
  intro s
  have hσ_lt : σ < (s : ℝ) + 1 := Nat.lt_floor_add_one σ
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    rw [hs_eq] at hσ_lt
    norm_num at hσ_lt
    linarith
  let s₀ : (i : Fin n) → (pulseToCounting P s).State i :=
    fun i => (Classical.arbitrary (P.State i), ⟨0, by omega⟩)
  let e := cleanExecution (pulseToCounting P s) s₀
  have he0 : AtMostCrashes e 0 := by
    dsimp only [AtMostCrashes]
    have hemp : Finset.univ.filter (fun i : Fin n => ∃ t, e.config t i = none) = ∅ := by
      ext i; simp [e, cleanExecution]
    simp [hemp]
  let i₀ : Fin n := ⟨0, by omega⟩
  refine ⟨e, he0, i₀, fun M => ?_⟩
  let eP := projExecution P s e
  have hePf : AtMostCrashes eP f :=
    le_trans (projExecution_atMostCrashes P s e he0) (Nat.zero_le f)
  obtain ⟨a, b, _, hk⟩ := nat_pulse_intervals hσ (hP eP hePf)
  have ha_ge : ∀ k, k ≤ a k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hab := (hk k).1
      have hsep := (hk k).2.2.2.1
      omega
  have hnfi₀ : Nonfaulty eP i₀ := by
    rw [projExecution_nonfaulty_iff]
    intro t; simp [e, cleanExecution]
  obtain ⟨t, ⟨hat, htb, hp_t⟩, huniq⟩ := (hk M).2.2.1 i₀ hnfi₀
  have hnp_t1 : ¬ Pulses eP i₀ (t + 1) := by
    intro hp1
    by_cases hlt : t < b M
    · have heq := huniq (t + 1) ⟨by omega, by omega, hp1⟩
      omega
    · have htb_eq : t = b M := by omega
      have hsep := (hk M).2.2.2.1
      exact (hk M).2.2.2.2 i₀ hnfi₀ (t + 1) (by omega) (by omega) hp1
  let sc_t := cleanStates (pulseToCounting P s) s₀ t i₀
  let sc_t1 := cleanStates (pulseToCounting P s) s₀ (t + 1) i₀
  have hcfg_t : e.config t i₀ = some sc_t := rfl
  have hcfg_t1 : e.config (t + 1) i₀ = some sc_t1 := rfl
  have hv0 : ((pulseToCounting P s).output i₀ sc_t).val = 0 :=
    counter_pulse_zero P s e i₀ t sc_t hcfg_t hp_t
  have hv1 : ((pulseToCounting P s).output i₀ sc_t1).val = 1 := by
    rw [counter_step_no_pulse P s e i₀ t sc_t sc_t1 hcfg_t hcfg_t1 hnp_t1, hv0]
    omega
  refine ⟨t, (ha_ge M).trans hat, sc_t, sc_t1, hcfg_t, hcfg_t1, ?_⟩
  intro heq
  have := congrArg Fin.val heq
  omega

/-- Lemma 8: `pulseToCounting P s` satisfies `LiftResilient` from round `T + 2 * s`. -/
lemma lemma_8 {n f T : ℕ} {σ : ℝ} (P : Protocol n Bool)
    (hσ : 1 ≤ σ) (hP : PulseResilient P f σ T) :
    let s := Nat.floor σ
    LiftResilient (pulseToCounting P s) f s (T + 2 * s) := by
  intro s e he_f
  have hσ_lt : σ < (s : ℝ) + 1 := Nat.lt_floor_add_one σ
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    rw [hs_eq] at hσ_lt
    norm_num at hσ_lt
    linarith
  let q : ℕ := 2 * s + 1
  let eP := projExecution P s e
  obtain ⟨a, b, ha0, hk⟩ := nat_pulse_intervals hσ (hP eP (projExecution_atMostCrashes P s e he_f))
  have ha_ge : ∀ k, k ≤ a k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hab := (hk k).1
      have hsep := (hk k).2.2.2.1
      omega
  -- Define τ i k ∈ [a k, b k] for non-faulty i
  let τ : Fin n → ℕ → ℕ := fun i k =>
    if hnf : Nonfaulty eP i then Classical.choose ((hk k).2.2.1 i hnf) else a k
  have hτ_spec : ∀ i, Nonfaulty eP i → ∀ k,
      (a k ≤ τ i k ∧ τ i k ≤ b k ∧ Pulses eP i (τ i k)) ∧
      (∀ t, a k ≤ t → t ≤ b k → Pulses eP i t → t = τ i k) := by
    intro i hnf k
    have hspec := Classical.choose_spec ((hk k).2.2.1 i hnf)
    have heq : τ i k = Classical.choose ((hk k).2.2.1 i hnf) := dif_pos hnf
    rw [heq]
    exact ⟨hspec.1, fun t h1 h2 hp => hspec.2 t ⟨h1, h2, hp⟩⟩
  have hτ_sep : ∀ i j, Nonfaulty eP i → Nonfaulty eP j → ∀ k, τ j k + s < τ i (k + 1) := by
    intro i j hnfi hnfj k
    have hjb : τ j k ≤ b k := ((hτ_spec j hnfj k).1).2.1
    have hai : a (k + 1) ≤ τ i (k + 1) := ((hτ_spec i hnfi (k + 1)).1).1
    have hsep := (hk k).2.2.2.1
    omega
  have hτ_skew : ∀ i j, Nonfaulty eP i → Nonfaulty eP j → ∀ k,
      |((τ i k : ℕ) : ℤ) - ((τ j k : ℕ) : ℤ)| ≤ (s : ℤ) := by
    intro i j hnfi hnfj k
    have hi := (hτ_spec i hnfi k).1
    have hj := (hτ_spec j hnfj k).1
    have hbw := (hk k).2.1
    have hab := (hk k).1
    rw [abs_le]
    omega
  have hτ_mono : ∀ i, Nonfaulty eP i → ∀ {k₁ k₂}, k₁ < k₂ → τ i k₁ < τ i k₂ := by
    intro i hnfi k₁ k₂ hlt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show k₁ + 1 ≤ k₂ by omega)
    induction d with
    | zero =>
      rw [Nat.add_zero]
      have := hτ_sep i i hnfi hnfi k₁
      omega
    | succ d ih =>
      have h1 := ih (by omega)
      have h2 := hτ_sep i i hnfi hnfi (k₁ + 1 + d)
      rw [show k₁ + 1 + (d + 1) = (k₁ + 1 + d) + 1 by omega]
      omega
  have hτ_mono_le : ∀ i, Nonfaulty eP i → ∀ {k₁ k₂}, k₁ ≤ k₂ → τ i k₁ ≤ τ i k₂ := by
    intro i hnfi k₁ k₂ hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact le_of_lt (hτ_mono i hnfi hlt)
    · exact le_refl _
  -- Complete characterization of pulses ≥ a 0
  have hpulse_iff : ∀ i, Nonfaulty eP i → ∀ t, a 0 ≤ t → (Pulses eP i t ↔ ∃ k, t = τ i k) := by
    intro i hnfi t hat0
    constructor
    · intro hpt
      suffices ∀ K, t < a K → ∃ m < K, t = τ i m by
        obtain ⟨m, _, hm⟩ := this (t + 1) (by have := ha_ge (t + 1); omega)
        exact ⟨m, hm⟩
      intro K
      induction K with
      | zero => intro hlt; omega
      | succ K ih =>
        intro hlt
        by_cases hltK : t < a K
        · obtain ⟨m, hmK, hm⟩ := ih hltK
          exact ⟨m, Nat.lt_succ_of_lt hmK, hm⟩
        · by_cases htbK : t ≤ b K
          · exact ⟨K, Nat.lt_succ_self K, (hτ_spec i hnfi K).2 t (by omega) htbK hpt⟩
          · exfalso
            exact (hk K).2.2.2.2 i hnfi t (by omega) hlt hpt
    · rintro ⟨k, rfl⟩
      exact ((hτ_spec i hnfi k).1).2.2
  -- Pulse counter N i t := smallest k with t < τ i k
  have hex_gt : ∀ i, Nonfaulty eP i → ∀ t, ∃ k, t < τ i k := by
    intro i hnfi t
    refine ⟨t + 1, ?_⟩
    have h1 := ha_ge (t + 1)
    have h2 := ((hτ_spec i hnfi (t + 1)).1).1
    omega
  let N : Fin n → ℕ → ℕ := fun i t =>
    if hnf : Nonfaulty eP i then Nat.find (hex_gt i hnf t) else 0
  have hN_gt : ∀ i (hnf : Nonfaulty eP i) t, t < τ i (N i t) := by
    intro i hnf t
    dsimp only [N]; rw [dif_pos hnf]
    exact Nat.find_spec (hex_gt i hnf t)
  have hN_le_of_lt : ∀ i (hnf : Nonfaulty eP i) t k, k < N i t → τ i k ≤ t := by
    intro i hnf t k hklt
    dsimp only [N] at hklt; rw [dif_pos hnf] at hklt
    exact not_lt.mp (Nat.find_min (hex_gt i hnf t) hklt)
  have hN_eq_iff : ∀ i (hnf : Nonfaulty eP i) t k,
      N i t = k ↔ t < τ i k ∧ ∀ m < k, τ i m ≤ t := by
    intro i hnf t k
    constructor
    · rintro rfl
      exact ⟨hN_gt i hnf t, fun m hm => hN_le_of_lt i hnf t m hm⟩
    · rintro ⟨hlt, hle_all⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h2
      · have := hle_all (N i t) h1
        have := hN_gt i hnf t
        omega
      · have := hN_le_of_lt i hnf t k h2
        omega
  -- Local counter value ϕ i t for non-faulty i
  let ϕ : Fin n → ℕ → ℕ := fun i t =>
    if h : (e.config t i).isSome then ((pulseToCounting P s).output i ((e.config t i).get h)).val else 0
  have hϕ_eq : ∀ i t sc, e.config t i = some sc → ϕ i t = ((pulseToCounting P s).output i sc).val := by
    intro i t sc hsc
    dsimp only [ϕ]
    have his : (e.config t i).isSome = true := by simp [hsc]
    rw [dif_pos his]
    congr 1; simp [hsc]
  have hϕ_le : ∀ i t, ϕ i t ≤ 2 * s := by
    intro i t; dsimp only [ϕ]
    split_ifs with his
    · have := ((pulseToCounting P s).output i ((e.config t i).get his)).isLt
      omega
    · omega
  have hϕ_pulse : ∀ i, Nonfaulty e i → ∀ t, Pulses eP i t → ϕ i t = 0 := by
    intro i hnf t hp
    obtain ⟨sc, hsc⟩ := Option.ne_none_iff_exists'.mp (hnf t)
    rw [hϕ_eq i t sc hsc]
    exact counter_pulse_zero P s e i t sc hsc hp
  have hϕ_no_pulse : ∀ i, Nonfaulty e i → ∀ t, ¬ Pulses eP i (t + 1) →
      ϕ i (t + 1) = min (2 * s) (ϕ i t + 1) := by
    intro i hnf t hnp
    obtain ⟨sc₀, hsc₀⟩ := Option.ne_none_iff_exists'.mp (hnf t)
    obtain ⟨sc₁, hsc₁⟩ := Option.ne_none_iff_exists'.mp (hnf (t + 1))
    rw [hϕ_eq i (t + 1) sc₁ hsc₁, hϕ_eq i t sc₀ hsc₀]
    exact counter_step_no_pulse P s e i t sc₀ sc₁ hsc₀ hsc₁ hnp
  have hϕ_after_pulse : ∀ i, Nonfaulty e i → ∀ r d,
      Pulses eP i r → (∀ u, r < u → u ≤ r + d → ¬ Pulses eP i u) →
      ϕ i (r + d) = min (2 * s) d := by
    intro i hnf r d hpr hno
    induction d with
    | zero => simp [hϕ_pulse i hnf r hpr]
    | succ d ih =>
      have ih' := ih (fun u h1 h2 => hno u h1 (by omega))
      have hnp := hno (r + d + 1) (by omega) (by omega)
      rw [show r + (d + 1) = (r + d) + 1 by omega, hϕ_no_pulse i hnf (r + d) hnp, ih']
      omega
  have hϕ_lower_no_pulse : ∀ i, Nonfaulty e i → ∀ r d,
      (∀ u, r < u → u ≤ r + d → ¬ Pulses eP i u) →
      min (2 * s) d ≤ ϕ i (r + d) := by
    intro i hnf r d hno
    induction d with
    | zero => simp
    | succ d ih =>
      have ih' := ih (fun u h1 h2 => hno u h1 (by omega))
      have hnp := hno (r + d + 1) (by omega) (by omega)
      rw [show r + (d + 1) = (r + d) + 1 by omega, hϕ_no_pulse i hnf (r + d) hnp]
      omega
  -- Unified lastPulse formula: ϕ i t = min (2 * s) (t - lastPulse i (N i t)) for t ≥ T + 2 * s
  let lastPulse : Fin n → ℕ → ℕ := fun i k =>
    match k with
    | 0 => T
    | m + 1 => τ i m
  have hlast_le : ∀ i, Nonfaulty e i → ∀ t, T + 2 * s ≤ t → lastPulse i (N i t) ≤ t := by
    intro i hnf t ht
    have hnfP : Nonfaulty eP i := (projExecution_nonfaulty_iff P s e i).mpr hnf
    cases hk_eq : N i t with
    | zero => dsimp only [lastPulse]; omega
    | succ m =>
      dsimp only [lastPulse]
      exact hN_le_of_lt i hnfP t m (by omega)
  have hϕ_formula : ∀ i, Nonfaulty e i → ∀ t, T + 2 * s ≤ t →
      ϕ i t = min (2 * s) (t - lastPulse i (N i t)) := by
    intro i hnf t ht
    have hnfP : Nonfaulty eP i := (projExecution_nonfaulty_iff P s e i).mpr hnf
    cases hk_eq : N i t with
    | zero =>
      dsimp only [lastPulse]
      have ht_lt : t < τ i 0 := hk_eq ▸ hN_gt i hnfP t
      have hno : ∀ u, a 0 < u → u ≤ a 0 + (t - a 0) → ¬ Pulses eP i u := by
        intro u hu1 hu2 hpu
        obtain ⟨m, rfl⟩ := (hpulse_iff i hnfP u (by omega)).mp hpu
        have := hτ_mono_le i hnfP (Nat.zero_le m)
        omega
      have hlow := hϕ_lower_no_pulse i hnf (a 0) (t - a 0) hno
      rw [show a 0 + (t - a 0) = t by omega] at hlow
      have hup := hϕ_le i t
      omega
    | succ m =>
      dsimp only [lastPulse]
      have hm_le : τ i m ≤ t := hN_le_of_lt i hnfP t m (by omega)
      have ht_lt : t < τ i (m + 1) := hk_eq ▸ hN_gt i hnfP t
      have hpm : Pulses eP i (τ i m) := ((hτ_spec i hnfP m).1).2.2
      have hno : ∀ u, τ i m < u → u ≤ τ i m + (t - τ i m) → ¬ Pulses eP i u := by
        intro u hu1 hu2 hpu
        have ha0_m : a 0 ≤ τ i m :=
          ((hτ_spec i hnfP 0).1).1.trans (hτ_mono_le i hnfP (Nat.zero_le m))
        obtain ⟨l, rfl⟩ := (hpulse_iff i hnfP u (by omega)).mp hpu
        rcases le_or_gt l m with hlm | hml
        · have := hτ_mono_le i hnfP hlm; omega
        · have := hτ_mono_le i hnfP (show m + 1 ≤ l by omega); omega
      have heq := hϕ_after_pulse i hnf (τ i m) (t - τ i m) hpm hno
      rwa [show τ i m + (t - τ i m) = t by omega] at heq
  -- Define the lift L i t := q * N i t + ϕ i t
  let L : Fin n → ℕ → ℤ := fun i t => (q : ℤ) * (N i t : ℤ) + (ϕ i t : ℤ)
  -- Helper for (L2) when N j t ≤ N i t
  have hL_diff_le : ∀ t, T + 2 * s ≤ t → ∀ i j, Nonfaulty e i → Nonfaulty e j →
      N j t ≤ N i t → |L i t - L j t| ≤ (s : ℤ) := by
    intro t ht i j hnfi hnfj hNle
    have hnfiP : Nonfaulty eP i := (projExecution_nonfaulty_iff P s e i).mpr hnfi
    have hnfjP : Nonfaulty eP j := (projExecution_nonfaulty_iff P s e j).mpr hnfj
    have hϕi := hϕ_formula i hnfi t ht
    have hϕj := hϕ_formula j hnfj t ht
    have hlpi := hlast_le i hnfi t ht
    have hlpj := hlast_le j hnfj t ht
    have ht_lt_j : t < τ j (N j t) := hN_gt j hnfjP t
    set k := N j t
    have hNi_lt : N i t < k + 2 := by
      by_contra hge
      have hle_t : τ i (k + 1) ≤ t := hN_le_of_lt i hnfiP t (k + 1) (by omega)
      have hsep := hτ_sep i j hnfiP hnfjP k
      omega
    rcases (show N i t = k ∨ N i t = k + 1 by omega) with hEq | hSucc
    · have hlp_skew : |(lastPulse i k : ℤ) - (lastPulse j k : ℤ)| ≤ (s : ℤ) := by
        rcases eq_zero_or_pos k with hk0 | hk_pos
        · rw [hk0]; simp [lastPulse]
        · obtain ⟨m, hm_eq⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          rw [hm_eq]; exact hτ_skew i j hnfiP hnfjP m
      have hL_sub : L i t - L j t = (ϕ i t : ℤ) - (ϕ j t : ℤ) := by
        dsimp only [L]; rw [hEq]; ring
      rw [hL_sub]
      rw [hEq] at hϕi hlpi
      rw [hϕi, hϕj]
      rw [abs_le] at hlp_skew ⊢
      omega
    · have hτik_le : τ i k ≤ t := hN_le_of_lt i hnfiP t k (by omega)
      have hskew_k := abs_le.mp (hτ_skew j i hnfjP hnfiP k)
      set m := t - τ i k with hm_def
      have hm_lt : m < s := by omega
      have hϕi_val : ϕ i t = m := by
        rw [hϕi, hSucc]
        dsimp only [lastPulse]
        omega
      have hlpj_gap : m + s + 1 ≤ t - lastPulse j k := by
        rcases eq_zero_or_pos k with hk0 | hk_pos
        · rw [hk0]; dsimp only [lastPulse]; omega
        · obtain ⟨l, hl_eq⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
          rw [hl_eq] at hτik_le hm_def ⊢
          dsimp only [lastPulse]
          have hsep := hτ_sep i j hnfiP hnfjP l
          omega
      have hϕj_low : m + s + 1 ≤ ϕ j t := by
        rw [hϕj]
        omega
      have hϕj_high : ϕ j t ≤ 2 * s := hϕ_le j t
      have hL_sub : L i t - L j t = (2 * s + 1 : ℤ) + (ϕ i t : ℤ) - (ϕ j t : ℤ) := by
        dsimp only [L, q]; rw [hSucc]; push_cast; ring
      rw [hL_sub, hϕi_val, abs_le]
      omega
  refine ⟨L, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · -- (L1) Compatibility
    intro i hnfi sc hsc
    rw [← hϕ_eq i t sc hsc]
    dsimp only [L, q]
    have hlt_q : (ϕ i t : ℤ) < ((2 * s + 1 : ℕ) : ℤ) := by have := hϕ_le i t; omega
    have hrew : ((2 * s + 1 : ℕ) : ℤ) * (N i t : ℤ) + (ϕ i t : ℤ) =
        (ϕ i t : ℤ) + (N i t : ℤ) * ((2 * s + 1 : ℕ) : ℤ) := by ring
    rw [hrew, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (Nat.cast_nonneg _) hlt_q]
  · -- (L2) σ-agreement
    intro i j hnfi hnfj
    rcases le_total (N j t) (N i t) with hle | hle
    · exact hL_diff_le t ht i j hnfi hnfj hle
    · rw [abs_sub_comm]
      exact hL_diff_le t ht j i hnfj hnfi hle
  · -- (L3) Bounded increments
    intro i hnfi
    have hnfiP : Nonfaulty eP i := (projExecution_nonfaulty_iff P s e i).mpr hnfi
    have ht_lt : t < τ i (N i t) := hN_gt i hnfiP t
    rcases lt_or_eq_of_le (show t + 1 ≤ τ i (N i t) by omega) with hlt1 | heq1
    · -- No pulse at t + 1
      have hnp1 : ¬ Pulses eP i (t + 1) := by
        intro hp1
        obtain ⟨m, hm⟩ := (hpulse_iff i hnfiP (t + 1) (by omega)).mp hp1
        rcases lt_or_ge m (N i t) with hm_lt | hm_ge
        · have := hN_le_of_lt i hnfiP t m hm_lt; omega
        · have := hτ_mono_le i hnfiP hm_ge; omega
      have hN_same : N i (t + 1) = N i t := by
        rw [hN_eq_iff i hnfiP (t + 1) (N i t)]
        exact ⟨hlt1, fun m hm => (hN_le_of_lt i hnfiP t m hm).trans (Nat.le_succ t)⟩
      have hϕ_step := hϕ_no_pulse i hnfi t hnp1
      have hϕ_ub := hϕ_le i t
      have hL_sub : L i (t + 1) - L i t = (ϕ i (t + 1) : ℤ) - (ϕ i t : ℤ) := by
        dsimp only [L]; rw [hN_same]; ring
      rw [hL_sub, hϕ_step]
      omega
    · -- Pulse at t + 1 = τ i (N i t)
      have hp1 : Pulses eP i (t + 1) := by
        rw [heq1]; exact ((hτ_spec i hnfiP (N i t)).1).2.2
      have hN_inc : N i (t + 1) = N i t + 1 := by
        rw [hN_eq_iff i hnfiP (t + 1) (N i t + 1)]
        refine ⟨?_, fun m hm => ?_⟩
        · have hsep := hτ_sep i i hnfiP hnfiP (N i t)
          omega
        · have hle_m : m ≤ N i t := by omega
          have := hτ_mono_le i hnfiP hle_m
          omega
      have hϕ1_zero : ϕ i (t + 1) = 0 := hϕ_pulse i hnfi (t + 1) hp1
      have hϕ_pos : 1 ≤ ϕ i t := by
        rw [hϕ_formula i hnfi t ht]
        rcases eq_zero_or_pos (N i t) with hk0 | hk_pos
        · rw [hk0]; dsimp only [lastPulse]; omega
        · obtain ⟨m, hm_eq⟩ : ∃ m, N i t = m + 1 := ⟨N i t - 1, by omega⟩
          rw [hm_eq] at heq1 ⊢
          dsimp only [lastPulse]
          have hsep := hτ_sep i i hnfiP hnfiP m
          omega
      have hϕ_ub := hϕ_le i t
      have hL_sub : L i (t + 1) - L i t = ((2 * s + 1 : ℕ) : ℤ) - (ϕ i t : ℤ) := by
        dsimp only [L, q]; rw [hN_inc, hϕ1_zero]; push_cast; ring
      rw [hL_sub]
      omega

/-- Theorem 2: Linear stabilisation lower bound for pulse synchronisation. -/
theorem theorem_2 {n f T : ℕ} (σ : ℝ) (P : Protocol n Bool)
    (hσ : 1 ≤ σ) (hn : f + 2 < n) (hP : PulseResilient P f σ T) :
    ((f / 2 : ℕ) : ℝ) < (T : ℝ) + 2 * σ := by
  by_contra hle
  push Not at hle
  let s : ℕ := Nat.floor σ
  have hs_le : (s : ℝ) ≤ σ := Nat.floor_le (by linarith)
  have hσ_lt : σ < (s : ℝ) + 1 := Nat.lt_floor_add_one σ
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    change σ < (s : ℝ) + 1 at hσ_lt
    rw [hs_eq] at hσ_lt
    norm_num at hσ_lt
    linarith
  have hT_le : T + 2 * s ≤ f / 2 := by
    have hreal : ((T + 2 * s : ℕ) : ℝ) ≤ ((f / 2 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.cast_le.mp hreal
  have hf1 : 1 ≤ f := by omega
  have hLift0 : LiftResilient (pulseToCounting P s) f s (T + 2 * s) :=
    lemma_8 P hσ hP
  have hLift : LiftResilient (pulseToCounting P s) f s (f / 2) := by
    intro e hef
    obtain ⟨L, hL⟩ := hLift0 e hef
    exact ⟨L, fun t ht => hL t (hT_le.trans ht)⟩
  have hNontriv : Nontrivial (pulseToCounting P s) :=
    pulseToCounting_nontrivial P hσ hn hP
  exact theorem_6 (pulseToCounting P s) hf1 hn (by omega) ⟨hLift, hNontriv⟩

end PulseSyncLowerBound.Pulse

end

open PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n f T : ℕ} (σ : ℝ) (P : Protocol n Bool)
    (hσ : 1 ≤ σ) (hn : f + 2 < n) (hP : PulseResilient P f σ T) :
    ((f / 2 : ℕ) : ℝ) < (T : ℝ) + 2 * σ :=
  PulseSyncLowerBound.Pulse.theorem_2 σ P hσ hn hP
